from __future__ import annotations

import re
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.generate_lean_all_modules_aggregate import tracked_module_names


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ROOT = REPO_ROOT / "formal" / "toe_formal"

_DECLARATION_KINDS = (
    "def",
    "abbrev",
    "opaque",
    "theorem",
    "lemma",
    "axiom",
    "constant",
    "structure",
    "class",
    "inductive",
    "coinductive",
)
_DECLARATION_MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
)
_MODIFIER_PATTERN = "|".join(_DECLARATION_MODIFIERS)
_KIND_PATTERN = "|".join(_DECLARATION_KINDS)

_DECLARATION_RE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*"
    rf"(?P<modifiers>(?:(?:{_MODIFIER_PATTERN})\s+)*)"
    rf"(?P<kind>{_KIND_PATTERN})\b(?P<tail>.*)$"
)
_INSTANCE_RE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*"
    rf"(?P<modifiers>(?:(?:{_MODIFIER_PATTERN}|local|scoped)\s+)*)"
    r"(?P<kind>instance)\b(?P<tail>.*)$"
)
_NAME_RE = re.compile(r"^(?P<name>[^\s:({\[=]+)")
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[^\s]+)\s*$")
_SECTION_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?section(?:\s+(?P<name>[^\s]+))?\s*$"
)
_MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+(?P<name>[^\s]+))?\s*$")


@dataclass(frozen=True)
class PublicDeclaration:
    fq_name: str
    kind: str
    module: str
    path: Path
    line: int


@dataclass(frozen=True)
class _Scope:
    kind: str
    namespace_components: tuple[str, ...] = ()


def _module_path(module: str) -> Path:
    return LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


def _without_comments_and_strings(source: str) -> list[str]:
    """Remove nested comments and strings while preserving source line numbers."""

    block_comment_depth = 0
    in_string = False
    escaped = False
    cleaned: list[str] = []

    for raw_line in source.splitlines():
        output: list[str] = []
        index = 0
        while index < len(raw_line):
            if block_comment_depth:
                if raw_line.startswith("/-", index):
                    block_comment_depth += 1
                    index += 2
                elif raw_line.startswith("-/", index):
                    block_comment_depth -= 1
                    index += 2
                else:
                    index += 1
                continue

            if in_string:
                char = raw_line[index]
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                index += 1
                continue

            if raw_line.startswith("--", index):
                break
            if raw_line.startswith("/-", index):
                block_comment_depth = 1
                index += 2
                continue
            if raw_line[index] == '"':
                in_string = True
                index += 1
                continue

            output.append(raw_line[index])
            index += 1

        # Lean string literals in this tree do not span physical lines. Resetting
        # here also prevents a malformed string from hiding later declarations.
        if in_string and not raw_line.rstrip().endswith("\\"):
            in_string = False
            escaped = False
        cleaned.append("".join(output))

    assert block_comment_depth == 0, "unterminated Lean block comment"
    return cleaned


def _declaration_head(line: str) -> tuple[str, str, bool] | None:
    match = _DECLARATION_RE.match(line) or _INSTANCE_RE.match(line)
    if match is None:
        return None
    modifiers = match.group("modifiers").split()
    return match.group("kind"), match.group("tail"), "private" in modifiers


def _name_from_tail(tail: str) -> str | None:
    stripped = tail.strip()
    if not stripped or stripped.startswith((":", "(", "[", "{")):
        # Anonymous instances and structure fields named like declaration
        # keywords do not introduce a user-selected public declaration name.
        return None
    match = _NAME_RE.match(stripped)
    return match.group("name") if match is not None else None


def _qualified_name(namespace: list[str], name: str) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    return ".".join([*namespace, name])


def _scan_module(module: str) -> list[PublicDeclaration]:
    path = _module_path(module)
    lines = _without_comments_and_strings(path.read_text(encoding="utf-8-sig"))
    namespace: list[str] = []
    scopes: list[_Scope] = []
    declarations: list[PublicDeclaration] = []
    pending: tuple[str, int, bool] | None = None

    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue

        if pending is not None:
            kind, declaration_line, is_private = pending
            name = _name_from_tail(line)
            assert name is not None, (
                f"unsupported multiline Lean declaration in {path}:{declaration_line}; "
                f"next code line is {line.strip()!r}"
            )
            if not is_private:
                declarations.append(
                    PublicDeclaration(
                        fq_name=_qualified_name(namespace, name),
                        kind=kind,
                        module=module,
                        path=path,
                        line=declaration_line,
                    )
                )
            pending = None
            continue

        namespace_match = _NAMESPACE_RE.match(line)
        if namespace_match is not None:
            components = tuple(namespace_match.group("name").split("."))
            namespace.extend(components)
            scopes.append(_Scope("namespace", components))
            continue

        if _SECTION_RE.match(line) is not None:
            scopes.append(_Scope("section"))
            continue
        if _MUTUAL_RE.match(line) is not None:
            scopes.append(_Scope("mutual"))
            continue
        if _END_RE.match(line) is not None:
            assert scopes, f"unmatched `end` in {path}:{line_number}"
            scope = scopes.pop()
            if scope.kind == "namespace":
                count = len(scope.namespace_components)
                assert tuple(namespace[-count:]) == scope.namespace_components
                del namespace[-count:]
            continue

        head = _declaration_head(line)
        if head is None:
            continue
        kind, tail, is_private = head
        if not tail.strip():
            pending = (kind, line_number, is_private)
            continue

        name = _name_from_tail(tail)
        if name is None:
            continue
        if not is_private:
            declarations.append(
                PublicDeclaration(
                    fq_name=_qualified_name(namespace, name),
                    kind=kind,
                    module=module,
                    path=path,
                    line=line_number,
                )
            )

    assert pending is None, f"declaration without a name at end of {path}"
    return declarations


@lru_cache(maxsize=1)
def _declaration_index() -> dict[str, list[PublicDeclaration]]:
    index: dict[str, list[PublicDeclaration]] = defaultdict(list)
    for module in tracked_module_names():
        for declaration in _scan_module(module):
            index[declaration.fq_name].append(declaration)
    return dict(index)


def _format_occurrences(occurrences: list[PublicDeclaration]) -> str:
    return ", ".join(
        f"{item.path.relative_to(REPO_ROOT).as_posix()}:{item.line} ({item.kind})"
        for item in occurrences
    )


def _assert_modules(
    index: dict[str, list[PublicDeclaration]], fq_name: str, expected: set[str]
) -> None:
    actual = {item.module for item in index.get(fq_name, [])}
    assert actual == expected, f"{fq_name}: expected {sorted(expected)}, found {sorted(actual)}"


def test_no_duplicate_public_fully_qualified_lean_declarations() -> None:
    index = _declaration_index()
    duplicates = {
        name: occurrences for name, occurrences in index.items() if len(occurrences) > 1
    }
    detail = "\n".join(
        f"{name}: {_format_occurrences(occurrences)}"
        for name, occurrences in sorted(duplicates.items())
    )
    assert not duplicates, "duplicate public Lean declarations:\n" + detail


def test_dispersion_variant_reuses_the_canonical_api_without_redeclaration() -> None:
    index = _declaration_index()
    canonical = "ToeFormal.CPNLSE2D.Dispersion"
    variant = "ToeFormal.CPNLSE2D.Dispersion_aristotle"
    for name in ("Field2D", "omega", "omega_expand", "planeWave"):
        _assert_modules(index, f"ToeFormal.CPNLSE2D.{name}", {canonical})
    _assert_modules(
        index,
        "ToeFormal.CPNLSE2D.DispersionAristotle.omega_recheck",
        {variant},
    )
    _assert_modules(
        index,
        "ToeFormal.CPNLSE2D.DispersionAristotle.planeWave_recheck",
        {variant},
    )


def test_ct01_variants_have_one_canonical_preservation_predicate() -> None:
    index = _declaration_index()
    abstract = "ToeFormal.Constraints.CT01_Abstract"
    probe = "ToeFormal.Constraints.CT01_LinearizationAt0"
    _assert_modules(
        index,
        "ToeFormal.Constraints.PreservesDR01_onPlaneWaves",
        {abstract},
    )
    for name in (
        "LinearizationAt0",
        "NoLinearPartAt0",
        "linearization_zero_implies_admissible",
        "CT01b_linearizationAt0_zero_preserves_DR01",
    ):
        _assert_modules(
            index,
            f"ToeFormal.Constraints.ProbeRelativeLinearizationAt0.{name}",
            {probe},
        )


def test_fn01_bridge_rechecks_the_canonical_consumer_under_a_child_namespace() -> None:
    index = _declaration_index()
    consumer = "ToeFormal.Constraints.FN01_CausalityCoreConsumer"
    bridge = "ToeFormal.Constraints.FN01_CausalityCoreBridge"
    for name in (
        "TimeOrder",
        "Admissible",
        "caus01_admissible_refl",
        "caus01_admissible_trans",
        "caus01_no_backward",
    ):
        _assert_modules(index, f"ToeFormal.Constraints.FN01.{name}", {consumer})
    for name in (
        "admissible_refl_recheck",
        "admissible_trans_recheck",
        "no_backward_recheck",
    ):
        _assert_modules(
            index,
            f"ToeFormal.Constraints.FN01.CausalityCoreBridge.{name}",
            {bridge},
        )


def test_p1_and_p2_parent_apis_are_variant_qualified() -> None:
    index = _declaration_index()
    p1 = "ToeFormal.Derivation.Parents.P1_NLS_EFT"
    p2 = "ToeFormal.Derivation.Parents.P2_Wave_EFT"
    shared_names = (
        "FieldC",
        "Dxx",
        "Dxxxx",
        "Dxxxxxx",
        "planeWave",
        "Dxx_planeWave",
        "Dxxxx_planeWave",
        "Dxxxxxx_planeWave",
    )
    for name in shared_names:
        _assert_modules(index, f"ToeFormal.Derivation.Parents.{name}", set())
        _assert_modules(index, f"ToeFormal.Derivation.Parents.P1NLS.{name}", {p1})
        _assert_modules(index, f"ToeFormal.Derivation.Parents.P2Wave.{name}", {p2})


def test_ucff_apis_are_variant_qualified() -> None:
    index = _declaration_index()
    modules = {
        "FirstOrder": "ToeFormal.UCFF.FirstOrder",
        "SecondOrderNumerics": "ToeFormal.UCFF.SecondOrderNumerics",
        "SecondOrderTimeDomain": "ToeFormal.UCFF.SecondOrderTimeDomain",
    }
    memberships = {
        "Field": tuple(modules),
        "Dxx": tuple(modules),
        "Dxxxx": tuple(modules),
        "Dxxxxxx": tuple(modules),
        "Dt": ("FirstOrder", "SecondOrderNumerics"),
        "absSq": ("FirstOrder", "SecondOrderNumerics"),
        "smulR": ("FirstOrder", "SecondOrderNumerics"),
    }
    for name, variants in memberships.items():
        _assert_modules(index, f"ToeFormal.UCFF.{name}", set())
        for variant in variants:
            _assert_modules(
                index,
                f"ToeFormal.UCFF.{variant}.{name}",
                {modules[variant]},
            )


def test_b1_and_b2_operator_agreement_assumptions_are_bridge_qualified() -> None:
    index = _declaration_index()
    b1 = "ToeFormal.Derivation.Bridges.B1_P1_to_UCFF_FirstOrderDispersion"
    b2 = "ToeFormal.Derivation.Bridges.B2_P2_to_UCFF_SecondOrderTimeDomain"
    for name in ("Dxx_agrees_spec", "Dxxxx_agrees_spec", "Dxxxxxx_agrees_spec"):
        _assert_modules(index, f"ToeFormal.Derivation.Bridges.{name}", set())
        _assert_modules(
            index,
            f"ToeFormal.Derivation.Bridges.B1P1FirstOrder.{name}",
            {b1},
        )
        _assert_modules(
            index,
            f"ToeFormal.Derivation.Bridges.B2P2SecondOrderTimeDomain.{name}",
            {b2},
        )
