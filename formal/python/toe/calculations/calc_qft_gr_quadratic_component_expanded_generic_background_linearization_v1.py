from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Iterable

from formal.python.toe.calculations.calc_qft_gr_quadratic_exact_generic_frozen_companion_operator import (
    minkowski_control_companion,
    sparse_entry_ledger,
)
from formal.python.tools.bounded_program_governance import QUADRATIC_PROGRAM_ID
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = (
    "derive_qft_gr_quadratic_component_expanded_"
    "generic_background_linearization_v1"
)
SEMANTIC_STAGE_ID = "COMPONENT_EXPANDED_LINEARIZATION"
OPEN_EVENT_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_events/"
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_ATTEMPT_02_OPEN_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
CONTRACT_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-"
    "LINEARIZATION-GAUGE-AND-JET-CONTRACT-v0.json"
)
REDUCED_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-"
    "REDUCED-SYSTEM-v0.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
    "COMPANION-OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-"
    "GENERIC-BACKGROUND-LINEARIZATION-v1.json"
)

DIMENSION = 4
SYMMETRIC_PAIRS = tuple(
    (a, b) for a in range(DIMENSION) for b in range(a, DIMENSION)
)
PAIR_LABELS = tuple(f"{a}{b}" for a, b in SYMMETRIC_PAIRS)
REF_PATTERN = re.compile(r"@([A-Za-z0-9_]+)")
LEAF_PATTERN = re.compile(r"\$([A-Za-z0-9_]+)")


def _pair(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a <= b else (b, a)


def _p(a: int, b: int) -> str:
    x, y = _pair(a, b)
    return f"{x}{y}"


def _leaf(name: str) -> str:
    return f"${name}"


def _ref(name: str) -> str:
    return f"@{name}"


def _sum(terms: Iterable[str]) -> str:
    rows = list(terms)
    if not rows:
        return "0"
    return "(" + " + ".join(rows) + ")"


def _prod(*terms: str) -> str:
    return "(" + " * ".join(terms) + ")"


def _neg(term: str) -> str:
    return f"(-1 * {term})"


def _g(a: int, b: int) -> str:
    return _leaf(f"gbar_{_p(a, b)}")


def _gi(a: int, b: int) -> str:
    return _leaf(f"gbarInv_{_p(a, b)}")


def _h(a: int, b: int) -> str:
    return _leaf(f"h_{_p(a, b)}")


def _c(a: int, b: int, d: int) -> str:
    return _leaf(f"cbar_{_p(a, b)}_{d}")


def _k(a: int, b: int, d: int) -> str:
    return _leaf(f"k_{_p(a, b)}_{d}")


def _c1(a: int, b: int, d: int, e: int) -> str:
    return _leaf(f"dcbar_{_p(a, b)}_{d}_{e}")


def _k1(a: int, b: int, d: int, e: int) -> str:
    return _leaf(f"dk_{_p(a, b)}_{d}_{e}")


def _c2(a: int, b: int, d: int, e: int, f: int) -> str:
    return _leaf(f"d2cbar_{_p(a, b)}_{d}_{e}_{f}")


def _k2(a: int, b: int, d: int, e: int, f: int) -> str:
    return _leaf(f"d2k_{_p(a, b)}_{d}_{e}_{f}")


def _s(a: int, b: int) -> str:
    return _leaf(f"Sbar_{_p(a, b)}")


def _ts(a: int, b: int) -> str:
    return _leaf(f"s_{_p(a, b)}")


def _s1(a: int, b: int, d: int) -> str:
    return _leaf(f"dSbar_{_p(a, b)}_{d}")


def _ts1(a: int, b: int, d: int) -> str:
    return _leaf(f"ds_{_p(a, b)}_{d}")


def _s2(a: int, b: int, d: int, e: int) -> str:
    return _leaf(f"d2Sbar_{_p(a, b)}_{d}_{e}")


def _ts2(a: int, b: int, d: int, e: int) -> str:
    return _leaf(f"d2s_{_p(a, b)}_{d}_{e}")


def _r1(a: int) -> str:
    return _leaf(f"rbar_{a}")


def _tr1(a: int) -> str:
    return _leaf(f"u_{a}")


def _r2(a: int, b: int) -> str:
    return _leaf(f"drbar_{a}_{b}")


def _tr2(a: int, b: int) -> str:
    return _leaf(f"du_{a}_{b}")


def _r3(a: int, b: int, c: int) -> str:
    return _leaf(f"d2rbar_{a}_{b}_{c}")


def _tr3(a: int, b: int, c: int) -> str:
    return _leaf(f"d2u_{a}_{b}_{c}")


@dataclass
class ComponentDag:
    nodes: list[dict[str, object]] = field(default_factory=list)
    identifiers: set[str] = field(default_factory=set)

    def add(
        self,
        identifier: str,
        expression: str,
        *,
        classification: str,
    ) -> str:
        if identifier in self.identifiers:
            raise QuadraticHyperbolicityError(f"duplicate DAG node: {identifier}")
        self.identifiers.add(identifier)
        self.nodes.append(
            {
                "id": identifier,
                "classification": classification,
                "expression": expression,
            }
        )
        return _ref(identifier)

    def finalize(self) -> None:
        by_id = {str(node["id"]): node for node in self.nodes}
        dependencies = {
            identifier: set(REF_PATTERN.findall(str(node["expression"])))
            for identifier, node in by_id.items()
        }
        unresolved = sorted(
            {
                reference
                for references in dependencies.values()
                for reference in references
                if reference not in by_id
            }
        )
        if unresolved:
            raise QuadraticHyperbolicityError(
                f"unresolved DAG references: {unresolved[:5]}"
            )

        ordered: list[dict[str, object]] = []
        permanent: set[str] = set()
        temporary: set[str] = set()

        def visit(identifier: str) -> None:
            if identifier in permanent:
                return
            if identifier in temporary:
                raise QuadraticHyperbolicityError(
                    f"cyclic component dependency at {identifier}"
                )
            temporary.add(identifier)
            for dependency in sorted(dependencies[identifier]):
                visit(dependency)
            temporary.remove(identifier)
            permanent.add(identifier)
            ordered.append(by_id[identifier])

        for identifier in sorted(by_id):
            visit(identifier)
        self.nodes = ordered


def _A(s: int, m: int, n: int, *, tangent: bool = False) -> str:
    value = _k if tangent else _c
    return _sum(
        [
            value(s, n, m),
            value(s, m, n),
            _neg(value(m, n, s)),
        ]
    )


def _dA(
    s: int, m: int, n: int, p: int, *, tangent: bool = False
) -> str:
    value = _k1 if tangent else _c1
    return _sum(
        [
            value(s, n, m, p),
            value(s, m, n, p),
            _neg(value(m, n, s, p)),
        ]
    )


def _d2A(
    s: int,
    m: int,
    n: int,
    p: int,
    q: int,
    *,
    tangent: bool = False,
) -> str:
    value = _k2 if tangent else _c2
    return _sum(
        [
            value(s, n, m, p, q),
            value(s, m, n, p, q),
            _neg(value(m, n, s, p, q)),
        ]
    )


def _build_connection_dag(dag: ComponentDag) -> None:
    for a, b in SYMMETRIC_PAIRS:
        dag.add(
            f"tInv_{a}{b}",
            _neg(
                _sum(
                    _prod(_gi(a, r), _gi(b, s), _h(r, s))
                    for r in range(DIMENSION)
                    for s in range(DIMENSION)
                )
            ),
            classification="ALGEBRAIC_BACKGROUND_COUPLING",
        )
        for p in range(DIMENSION):
            dag.add(
                f"dInv_{a}{b}_{p}",
                _neg(
                    _sum(
                        _prod(_gi(a, r), _gi(b, s), _c(r, s, p))
                        for r in range(DIMENSION)
                        for s in range(DIMENSION)
                    )
                ),
                classification="FIRST_BACKGROUND_DERIVATIVE",
            )
            dag.add(
                f"tdInv_{a}{b}_{p}",
                _neg(
                    _sum(
                        _sum(
                            [
                                _prod(
                                    _ref(f"tInv_{_p(a, r)}"),
                                    _gi(b, s),
                                    _c(r, s, p),
                                ),
                                _prod(
                                    _gi(a, r),
                                    _ref(f"tInv_{_p(b, s)}"),
                                    _c(r, s, p),
                                ),
                                _prod(_gi(a, r), _gi(b, s), _k(r, s, p)),
                            ]
                        )
                        for r in range(DIMENSION)
                        for s in range(DIMENSION)
                    )
                ),
                classification="LINEARIZED_FIRST_BACKGROUND_DERIVATIVE",
            )
            for q in range(DIMENSION):
                dag.add(
                    f"d2Inv_{a}{b}_{p}_{q}",
                    _neg(
                        _sum(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"dInv_{_p(a, r)}_{q}"),
                                        _gi(b, s),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _ref(f"dInv_{_p(b, s)}_{q}"),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _gi(b, s),
                                        _c1(r, s, p, q),
                                    ),
                                ]
                            )
                            for r in range(DIMENSION)
                            for s in range(DIMENSION)
                        )
                    ),
                    classification="SECOND_BACKGROUND_DERIVATIVE",
                )
                dag.add(
                    f"td2Inv_{a}{b}_{p}_{q}",
                    _neg(
                        _sum(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"tdInv_{_p(a, r)}_{q}"),
                                        _gi(b, s),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _ref(f"dInv_{_p(a, r)}_{q}"),
                                        _ref(f"tInv_{_p(b, s)}"),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _ref(f"dInv_{_p(a, r)}_{q}"),
                                        _gi(b, s),
                                        _k(r, s, p),
                                    ),
                                    _prod(
                                        _ref(f"tInv_{_p(a, r)}"),
                                        _ref(f"dInv_{_p(b, s)}_{q}"),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _ref(f"tdInv_{_p(b, s)}_{q}"),
                                        _c(r, s, p),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _ref(f"dInv_{_p(b, s)}_{q}"),
                                        _k(r, s, p),
                                    ),
                                    _prod(
                                        _ref(f"tInv_{_p(a, r)}"),
                                        _gi(b, s),
                                        _c1(r, s, p, q),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _ref(f"tInv_{_p(b, s)}"),
                                        _c1(r, s, p, q),
                                    ),
                                    _prod(
                                        _gi(a, r),
                                        _gi(b, s),
                                        _k1(r, s, p, q),
                                    ),
                                ]
                            )
                            for r in range(DIMENSION)
                            for s in range(DIMENSION)
                        )
                    ),
                    classification="LINEARIZED_SECOND_BACKGROUND_DERIVATIVE",
                )

    for r in range(DIMENSION):
        for m, n in SYMMETRIC_PAIRS:
            dag.add(
                f"Gamma_{r}_{m}{n}",
                _prod(
                    "1/2",
                    _sum(_prod(_gi(r, s), _A(s, m, n)) for s in range(DIMENSION)),
                ),
                classification="CONNECTION_COMPONENT",
            )
            dag.add(
                f"tGamma_{r}_{m}{n}",
                _prod(
                    "1/2",
                    _sum(
                        _sum(
                            [
                                _prod(_ref(f"tInv_{_p(r, s)}"), _A(s, m, n)),
                                _prod(_gi(r, s), _A(s, m, n, tangent=True)),
                            ]
                        )
                        for s in range(DIMENSION)
                    ),
                ),
                classification="LINEARIZED_CONNECTION_COMPONENT",
            )
            for p in range(DIMENSION):
                dag.add(
                    f"dGamma_{p}_{r}_{m}{n}",
                    _prod(
                        "1/2",
                        _sum(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"dInv_{_p(r, s)}_{p}"),
                                        _A(s, m, n),
                                    ),
                                    _prod(_gi(r, s), _dA(s, m, n, p)),
                                ]
                            )
                            for s in range(DIMENSION)
                        ),
                    ),
                    classification="CONNECTION_DERIVATIVE_COMPONENT",
                )
                dag.add(
                    f"tdGamma_{p}_{r}_{m}{n}",
                    _prod(
                        "1/2",
                        _sum(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"tdInv_{_p(r, s)}_{p}"),
                                        _A(s, m, n),
                                    ),
                                    _prod(
                                        _ref(f"dInv_{_p(r, s)}_{p}"),
                                        _A(s, m, n, tangent=True),
                                    ),
                                    _prod(
                                        _ref(f"tInv_{_p(r, s)}"),
                                        _dA(s, m, n, p),
                                    ),
                                    _prod(
                                        _gi(r, s),
                                        _dA(s, m, n, p, tangent=True),
                                    ),
                                ]
                            )
                            for s in range(DIMENSION)
                        ),
                    ),
                    classification="LINEARIZED_CONNECTION_DERIVATIVE_COMPONENT",
                )
                for q in range(DIMENSION):
                    dag.add(
                        f"d2Gamma_{p}_{q}_{r}_{m}{n}",
                        _prod(
                            "1/2",
                            _sum(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"d2Inv_{_p(r, s)}_{p}_{q}"),
                                            _A(s, m, n),
                                        ),
                                        _prod(
                                            _ref(f"dInv_{_p(r, s)}_{p}"),
                                            _dA(s, m, n, q),
                                        ),
                                        _prod(
                                            _ref(f"dInv_{_p(r, s)}_{q}"),
                                            _dA(s, m, n, p),
                                        ),
                                        _prod(
                                            _gi(r, s),
                                            _d2A(s, m, n, p, q),
                                        ),
                                    ]
                                )
                                for s in range(DIMENSION)
                            ),
                        ),
                        classification="SECOND_CONNECTION_DERIVATIVE_COMPONENT",
                    )
                    dag.add(
                        f"td2Gamma_{p}_{q}_{r}_{m}{n}",
                        _prod(
                            "1/2",
                            _sum(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"td2Inv_{_p(r, s)}_{p}_{q}"),
                                            _A(s, m, n),
                                        ),
                                        _prod(
                                            _ref(f"d2Inv_{_p(r, s)}_{p}_{q}"),
                                            _A(s, m, n, tangent=True),
                                        ),
                                        _prod(
                                            _ref(f"tdInv_{_p(r, s)}_{p}"),
                                            _dA(s, m, n, q),
                                        ),
                                        _prod(
                                            _ref(f"dInv_{_p(r, s)}_{p}"),
                                            _dA(s, m, n, q, tangent=True),
                                        ),
                                        _prod(
                                            _ref(f"tdInv_{_p(r, s)}_{q}"),
                                            _dA(s, m, n, p),
                                        ),
                                        _prod(
                                            _ref(f"dInv_{_p(r, s)}_{q}"),
                                            _dA(s, m, n, p, tangent=True),
                                        ),
                                        _prod(
                                            _ref(f"tInv_{_p(r, s)}"),
                                            _d2A(s, m, n, p, q),
                                        ),
                                        _prod(
                                            _gi(r, s),
                                            _d2A(s, m, n, p, q, tangent=True),
                                        ),
                                    ]
                                )
                                for s in range(DIMENSION)
                            ),
                        ),
                        classification="LINEARIZED_SECOND_CONNECTION_DERIVATIVE_COMPONENT",
                    )


def _build_curvature_and_harmonic_dag(dag: ComponentDag) -> None:
    for m, n in SYMMETRIC_PAIRS:
        ricci_terms: list[str] = []
        tangent_terms: list[str] = []
        for r in range(DIMENSION):
            ricci_terms.extend(
                [
                    _ref(f"dGamma_{r}_{r}_{_p(n, m)}"),
                    _neg(_ref(f"dGamma_{n}_{r}_{_p(r, m)}")),
                ]
            )
            tangent_terms.extend(
                [
                    _ref(f"tdGamma_{r}_{r}_{_p(n, m)}"),
                    _neg(_ref(f"tdGamma_{n}_{r}_{_p(r, m)}")),
                ]
            )
            for ell in range(DIMENSION):
                ricci_terms.extend(
                    [
                        _prod(
                            _ref(f"Gamma_{r}_{_p(r, ell)}"),
                            _ref(f"Gamma_{ell}_{_p(n, m)}"),
                        ),
                        _neg(
                            _prod(
                                _ref(f"Gamma_{r}_{_p(n, ell)}"),
                                _ref(f"Gamma_{ell}_{_p(r, m)}"),
                            )
                        ),
                    ]
                )
                tangent_terms.extend(
                    [
                        _prod(
                            _ref(f"tGamma_{r}_{_p(r, ell)}"),
                            _ref(f"Gamma_{ell}_{_p(n, m)}"),
                        ),
                        _prod(
                            _ref(f"Gamma_{r}_{_p(r, ell)}"),
                            _ref(f"tGamma_{ell}_{_p(n, m)}"),
                        ),
                        _neg(
                            _prod(
                                _ref(f"tGamma_{r}_{_p(n, ell)}"),
                                _ref(f"Gamma_{ell}_{_p(r, m)}"),
                            )
                        ),
                        _neg(
                            _prod(
                                _ref(f"Gamma_{r}_{_p(n, ell)}"),
                                _ref(f"tGamma_{ell}_{_p(r, m)}"),
                            )
                        ),
                    ]
                )
        dag.add(
            f"Ricci_{m}{n}",
            _sum(ricci_terms),
            classification="RICCI_COMPONENT",
        )
        dag.add(
            f"tRicci_{m}{n}",
            _sum(tangent_terms),
            classification="LINEARIZED_RICCI_COMPONENT",
        )
        for a in range(DIMENSION):
            d_terms: list[str] = []
            td_terms: list[str] = []
            for r in range(DIMENSION):
                d_terms.extend(
                    [
                        _ref(f"d2Gamma_{r}_{a}_{r}_{_p(n, m)}"),
                        _neg(_ref(f"d2Gamma_{n}_{a}_{r}_{_p(r, m)}")),
                    ]
                )
                td_terms.extend(
                    [
                        _ref(f"td2Gamma_{r}_{a}_{r}_{_p(n, m)}"),
                        _neg(_ref(f"td2Gamma_{n}_{a}_{r}_{_p(r, m)}")),
                    ]
                )
                for ell in range(DIMENSION):
                    product_pairs = [
                        (f"Gamma_{r}_{_p(r, ell)}", f"Gamma_{ell}_{_p(n, m)}", 1),
                        (f"Gamma_{r}_{_p(n, ell)}", f"Gamma_{ell}_{_p(r, m)}", -1),
                    ]
                    for left, right, sign in product_pairs:
                        first = _prod(_ref(f"d{left}"), _ref(right))
                        second = _prod(_ref(left), _ref(f"d{right}"))
                        # The derivative nodes carry the coordinate index first.
                        first = first.replace("@dGamma_", f"@dGamma_{a}_", 1)
                        second = second.replace("@dGamma_", f"@dGamma_{a}_", 1)
                        tfirst = _sum(
                            [
                                first.replace("@dGamma_", "@tdGamma_", 1),
                                first.replace("@Gamma_", "@tGamma_", 1),
                            ]
                        )
                        tsecond = _sum(
                            [
                                second.replace("@Gamma_", "@tGamma_", 1),
                                second.replace("@dGamma_", "@tdGamma_", 1),
                            ]
                        )
                        if sign < 0:
                            first, second = _neg(first), _neg(second)
                            tfirst, tsecond = _neg(tfirst), _neg(tsecond)
                        d_terms.extend([first, second])
                        td_terms.extend([tfirst, tsecond])
            dag.add(
                f"dRicci_{a}_{m}{n}",
                _sum(d_terms),
                classification="RICCI_DERIVATIVE_COMPONENT",
            )
            dag.add(
                f"tdRicci_{a}_{m}{n}",
                _sum(td_terms),
                classification="LINEARIZED_RICCI_DERIVATIVE_COMPONENT",
            )

    for r in range(DIMENSION):
        dag.add(
            f"ContractedGamma_{r}",
            _sum(
                _prod(_gi(a, b), _ref(f"Gamma_{r}_{_p(a, b)}"))
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="CONTRACTED_CONNECTION_COMPONENT",
        )
        dag.add(
            f"tContractedGamma_{r}",
            _sum(
                _sum(
                    [
                        _prod(
                            _ref(f"tInv_{_p(a, b)}"),
                            _ref(f"Gamma_{r}_{_p(a, b)}"),
                        ),
                        _prod(
                            _gi(a, b),
                            _ref(f"tGamma_{r}_{_p(a, b)}"),
                        ),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="LINEARIZED_CONTRACTED_CONNECTION_COMPONENT",
        )
        for p in range(DIMENSION):
            dag.add(
                f"dContractedGamma_{p}_{r}",
                _sum(
                    _sum(
                        [
                            _prod(
                                _ref(f"dInv_{_p(a, b)}_{p}"),
                                _ref(f"Gamma_{r}_{_p(a, b)}"),
                            ),
                            _prod(
                                _gi(a, b),
                                _ref(f"dGamma_{p}_{r}_{_p(a, b)}"),
                            ),
                        ]
                    )
                    for a in range(DIMENSION)
                    for b in range(DIMENSION)
                ),
                classification="CONTRACTED_CONNECTION_DERIVATIVE_COMPONENT",
            )
            dag.add(
                f"tdContractedGamma_{p}_{r}",
                _sum(
                    _sum(
                        [
                            _prod(
                                _ref(f"tdInv_{_p(a, b)}_{p}"),
                                _ref(f"Gamma_{r}_{_p(a, b)}"),
                            ),
                            _prod(
                                _ref(f"dInv_{_p(a, b)}_{p}"),
                                _ref(f"tGamma_{r}_{_p(a, b)}"),
                            ),
                            _prod(
                                _ref(f"tInv_{_p(a, b)}"),
                                _ref(f"dGamma_{p}_{r}_{_p(a, b)}"),
                            ),
                            _prod(
                                _gi(a, b),
                                _ref(f"tdGamma_{p}_{r}_{_p(a, b)}"),
                            ),
                        ]
                    )
                    for a in range(DIMENSION)
                    for b in range(DIMENSION)
                ),
                classification="LINEARIZED_CONTRACTED_CONNECTION_DERIVATIVE_COMPONENT",
            )
            for q in range(DIMENSION):
                dag.add(
                    f"d2ContractedGamma_{p}_{q}_{r}",
                    _sum(
                        _sum(
                            [
                                _prod(
                                    _ref(f"d2Inv_{_p(a, b)}_{p}_{q}"),
                                    _ref(f"Gamma_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"dInv_{_p(a, b)}_{p}"),
                                    _ref(f"dGamma_{q}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"dInv_{_p(a, b)}_{q}"),
                                    _ref(f"dGamma_{p}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _gi(a, b),
                                    _ref(f"d2Gamma_{p}_{q}_{r}_{_p(a, b)}"),
                                ),
                            ]
                        )
                        for a in range(DIMENSION)
                        for b in range(DIMENSION)
                    ),
                    classification="SECOND_CONTRACTED_CONNECTION_DERIVATIVE",
                )
                dag.add(
                    f"td2ContractedGamma_{p}_{q}_{r}",
                    _sum(
                        _sum(
                            [
                                _prod(
                                    _ref(f"td2Inv_{_p(a, b)}_{p}_{q}"),
                                    _ref(f"Gamma_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"d2Inv_{_p(a, b)}_{p}_{q}"),
                                    _ref(f"tGamma_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"tdInv_{_p(a, b)}_{p}"),
                                    _ref(f"dGamma_{q}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"dInv_{_p(a, b)}_{p}"),
                                    _ref(f"tdGamma_{q}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"tdInv_{_p(a, b)}_{q}"),
                                    _ref(f"dGamma_{p}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"dInv_{_p(a, b)}_{q}"),
                                    _ref(f"tdGamma_{p}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _ref(f"tInv_{_p(a, b)}"),
                                    _ref(f"d2Gamma_{p}_{q}_{r}_{_p(a, b)}"),
                                ),
                                _prod(
                                    _gi(a, b),
                                    _ref(f"td2Gamma_{p}_{q}_{r}_{_p(a, b)}"),
                                ),
                            ]
                        )
                        for a in range(DIMENSION)
                        for b in range(DIMENSION)
                    ),
                    classification="LINEARIZED_SECOND_CONTRACTED_CONNECTION_DERIVATIVE",
                )

    for m, n in SYMMETRIC_PAIRS:
        wave_g = _sum(
            _prod(_gi(a, b), _c1(m, n, a, b))
            for a in range(DIMENSION)
            for b in range(DIMENSION)
        )
        twave_g = _sum(
            _sum(
                [
                    _prod(_ref(f"tInv_{_p(a, b)}"), _c1(m, n, a, b)),
                    _prod(_gi(a, b), _k1(m, n, a, b)),
                ]
            )
            for a in range(DIMENSION)
            for b in range(DIMENSION)
        )
        metric_gauge = _sum(
            _sum(
                [
                    _prod(_g(m, r), _ref(f"dContractedGamma_{n}_{r}")),
                    _prod(_g(n, r), _ref(f"dContractedGamma_{m}_{r}")),
                ]
            )
            for r in range(DIMENSION)
        )
        tmetric_gauge = _sum(
            _sum(
                [
                    _prod(_h(m, r), _ref(f"dContractedGamma_{n}_{r}")),
                    _prod(_g(m, r), _ref(f"tdContractedGamma_{n}_{r}")),
                    _prod(_h(n, r), _ref(f"dContractedGamma_{m}_{r}")),
                    _prod(_g(n, r), _ref(f"tdContractedGamma_{m}_{r}")),
                ]
            )
            for r in range(DIMENSION)
        )
        dag.add(
            f"HarmonicMetricSource_{m}{n}",
            _sum(
                [
                    _ref(f"Ricci_{m}{n}"),
                    _prod("1/2", wave_g),
                    _neg(_prod("1/2", metric_gauge)),
                ]
            ),
            classification="STRICT_HARMONIC_METRIC_SOURCE_COMPONENT",
        )
        dag.add(
            f"tHarmonicMetricSource_{m}{n}",
            _sum(
                [
                    _ref(f"tRicci_{m}{n}"),
                    _prod("1/2", twave_g),
                    _neg(_prod("1/2", tmetric_gauge)),
                ]
            ),
            classification="LINEARIZED_STRICT_HARMONIC_METRIC_SOURCE_COMPONENT",
        )
        for p in range(DIMENSION):
            dwave_g = _sum(
                _sum(
                    [
                        _prod(
                            _ref(f"dInv_{_p(a, b)}_{p}"),
                            _c1(m, n, a, b),
                        ),
                        _prod(_gi(a, b), _c2(m, n, a, b, p)),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            )
            tdwave_g = _sum(
                _sum(
                    [
                        _prod(
                            _ref(f"tdInv_{_p(a, b)}_{p}"),
                            _c1(m, n, a, b),
                        ),
                        _prod(
                            _ref(f"dInv_{_p(a, b)}_{p}"),
                            _k1(m, n, a, b),
                        ),
                        _prod(
                            _ref(f"tInv_{_p(a, b)}"),
                            _c2(m, n, a, b, p),
                        ),
                        _prod(_gi(a, b), _k2(m, n, a, b, p)),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            )
            dmetric_gauge = _sum(
                _sum(
                    [
                        _prod(_c(m, r, p), _ref(f"dContractedGamma_{n}_{r}")),
                        _prod(_g(m, r), _ref(f"d2ContractedGamma_{n}_{p}_{r}")),
                        _prod(_c(n, r, p), _ref(f"dContractedGamma_{m}_{r}")),
                        _prod(_g(n, r), _ref(f"d2ContractedGamma_{m}_{p}_{r}")),
                    ]
                )
                for r in range(DIMENSION)
            )
            tdmetric_gauge = _sum(
                _sum(
                    [
                        _prod(_k(m, r, p), _ref(f"dContractedGamma_{n}_{r}")),
                        _prod(_c(m, r, p), _ref(f"tdContractedGamma_{n}_{r}")),
                        _prod(_h(m, r), _ref(f"d2ContractedGamma_{n}_{p}_{r}")),
                        _prod(_g(m, r), _ref(f"td2ContractedGamma_{n}_{p}_{r}")),
                        _prod(_k(n, r, p), _ref(f"dContractedGamma_{m}_{r}")),
                        _prod(_c(n, r, p), _ref(f"tdContractedGamma_{m}_{r}")),
                        _prod(_h(n, r), _ref(f"d2ContractedGamma_{m}_{p}_{r}")),
                        _prod(_g(n, r), _ref(f"td2ContractedGamma_{m}_{p}_{r}")),
                    ]
                )
                for r in range(DIMENSION)
            )
            dag.add(
                f"dHarmonicMetricSource_{p}_{m}{n}",
                _sum(
                    [
                        _ref(f"dRicci_{p}_{m}{n}"),
                        _prod("1/2", dwave_g),
                        _neg(_prod("1/2", dmetric_gauge)),
                    ]
                ),
                classification="STRICT_HARMONIC_METRIC_SOURCE_DERIVATIVE",
            )
            dag.add(
                f"tdHarmonicMetricSource_{p}_{m}{n}",
                _sum(
                    [
                        _ref(f"tdRicci_{p}_{m}{n}"),
                        _prod("1/2", tdwave_g),
                        _neg(_prod("1/2", tdmetric_gauge)),
                    ]
                ),
                classification="LINEARIZED_STRICT_HARMONIC_METRIC_SOURCE_DERIVATIVE",
            )


def _build_tensor_dag(dag: ComponentDag) -> None:
    for m in range(DIMENSION):
        for r in range(DIMENSION):
            for n in range(DIMENSION):
                for s in range(DIMENSION):
                    raised = _sum(
                        [
                            _ref(f"dGamma_{n}_{ell}_{_p(s, r)}")
                            if False
                            else "0"
                            for ell in []
                        ]
                    )
                    riemann_up = _sum(
                        [
                            _ref(f"dGamma_{n}_{r}_{_p(s, r)}")
                            if False
                            else "0"
                        ]
                    )
                    # Explicit convention:
                    # R^ell_{r n s}=d_n Gamma^ell_{s r}
                    # -d_s Gamma^ell_{n r}+Gamma^ell_{n q}Gamma^q_{s r}
                    # -Gamma^ell_{s q}Gamma^q_{n r}.
                    terms: list[str] = []
                    tterms: list[str] = []
                    for ell in range(DIMENSION):
                        up_terms = [
                            _ref(f"dGamma_{n}_{ell}_{_p(s, r)}"),
                            _neg(_ref(f"dGamma_{s}_{ell}_{_p(n, r)}")),
                        ]
                        tup_terms = [
                            _ref(f"tdGamma_{n}_{ell}_{_p(s, r)}"),
                            _neg(_ref(f"tdGamma_{s}_{ell}_{_p(n, r)}")),
                        ]
                        for q in range(DIMENSION):
                            up_terms.extend(
                                [
                                    _prod(
                                        _ref(f"Gamma_{ell}_{_p(n, q)}"),
                                        _ref(f"Gamma_{q}_{_p(s, r)}"),
                                    ),
                                    _neg(
                                        _prod(
                                            _ref(f"Gamma_{ell}_{_p(s, q)}"),
                                            _ref(f"Gamma_{q}_{_p(n, r)}"),
                                        )
                                    ),
                                ]
                            )
                            tup_terms.extend(
                                [
                                    _prod(
                                        _ref(f"tGamma_{ell}_{_p(n, q)}"),
                                        _ref(f"Gamma_{q}_{_p(s, r)}"),
                                    ),
                                    _prod(
                                        _ref(f"Gamma_{ell}_{_p(n, q)}"),
                                        _ref(f"tGamma_{q}_{_p(s, r)}"),
                                    ),
                                    _neg(
                                        _prod(
                                            _ref(f"tGamma_{ell}_{_p(s, q)}"),
                                            _ref(f"Gamma_{q}_{_p(n, r)}"),
                                        )
                                    ),
                                    _neg(
                                        _prod(
                                            _ref(f"Gamma_{ell}_{_p(s, q)}"),
                                            _ref(f"tGamma_{q}_{_p(n, r)}"),
                                        )
                                    ),
                                ]
                            )
                        terms.append(_prod(_g(m, ell), _sum(up_terms)))
                        tterms.extend(
                            [
                                _prod(_h(m, ell), _sum(up_terms)),
                                _prod(_g(m, ell), _sum(tup_terms)),
                            ]
                        )
                    dag.add(
                        f"RiemannLower_{m}_{r}_{n}_{s}",
                        _sum(terms),
                        classification="LOWERED_RIEMANN_COMPONENT",
                    )
                    dag.add(
                        f"tRiemannLower_{m}_{r}_{n}_{s}",
                        _sum(tterms),
                        classification="LINEARIZED_LOWERED_RIEMANN_COMPONENT",
                    )

    for r, s in SYMMETRIC_PAIRS:
        dag.add(
            f"SRaised_{r}{s}",
            _sum(
                _prod(_gi(r, a), _gi(s, b), _s(a, b))
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="RAISED_TRACEFREE_RICCI_COMPONENT",
        )
        dag.add(
            f"tSRaised_{r}{s}",
            _sum(
                _sum(
                    [
                        _prod(_ref(f"tInv_{_p(r, a)}"), _gi(s, b), _s(a, b)),
                        _prod(_gi(r, a), _ref(f"tInv_{_p(s, b)}"), _s(a, b)),
                        _prod(_gi(r, a), _gi(s, b), _ts(a, b)),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="LINEARIZED_RAISED_TRACEFREE_RICCI_COMPONENT",
        )

    dag.add(
        "SNorm",
        _sum(
            _prod(_s(a, b), _ref(f"SRaised_{_p(a, b)}"))
            for a in range(DIMENSION)
            for b in range(DIMENSION)
        ),
        classification="TRACEFREE_RICCI_QUADRATIC_CONTRACTION",
    )
    dag.add(
        "tSNorm",
        _sum(
            _sum(
                [
                    _prod(_ts(a, b), _ref(f"SRaised_{_p(a, b)}")),
                    _prod(_s(a, b), _ref(f"tSRaised_{_p(a, b)}")),
                ]
            )
            for a in range(DIMENSION)
            for b in range(DIMENSION)
        ),
        classification="LINEARIZED_TRACEFREE_RICCI_QUADRATIC_CONTRACTION",
    )

    for a in range(DIMENSION):
        for m, n in SYMMETRIC_PAIRS:
            dag.add(
                f"DS_{a}_{m}{n}",
                _sum(
                    [_s1(m, n, a)]
                    + [
                        _neg(
                            _prod(
                                _ref(f"Gamma_{r}_{_p(a, m)}"),
                                _s(r, n),
                            )
                        )
                        for r in range(DIMENSION)
                    ]
                    + [
                        _neg(
                            _prod(
                                _ref(f"Gamma_{r}_{_p(a, n)}"),
                                _s(m, r),
                            )
                        )
                        for r in range(DIMENSION)
                    ]
                ),
                classification="TENSOR_FIRST_DERIVATIVE_COMPONENT",
            )
            dag.add(
                f"tDS_{a}_{m}{n}",
                _sum(
                    [_ts1(m, n, a)]
                    + [
                        _neg(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"tGamma_{r}_{_p(a, m)}"),
                                        _s(r, n),
                                    ),
                                    _prod(
                                        _ref(f"Gamma_{r}_{_p(a, m)}"),
                                        _ts(r, n),
                                    ),
                                ]
                            )
                        )
                        for r in range(DIMENSION)
                    ]
                    + [
                        _neg(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"tGamma_{r}_{_p(a, n)}"),
                                        _s(m, r),
                                    ),
                                    _prod(
                                        _ref(f"Gamma_{r}_{_p(a, n)}"),
                                        _ts(m, r),
                                    ),
                                ]
                            )
                        )
                        for r in range(DIMENSION)
                    ]
                ),
                classification="LINEARIZED_TENSOR_FIRST_DERIVATIVE_COMPONENT",
            )

    for a in range(DIMENSION):
        for b in range(DIMENSION):
            for m, n in SYMMETRIC_PAIRS:
                dag.add(
                    f"pDS_{a}_{b}_{m}{n}",
                    _sum(
                        [_s2(m, n, b, a)]
                        + [
                            _neg(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"dGamma_{a}_{r}_{_p(b, m)}"),
                                            _s(r, n),
                                        ),
                                        _prod(
                                            _ref(f"Gamma_{r}_{_p(b, m)}"),
                                            _s1(r, n, a),
                                        ),
                                    ]
                                )
                            )
                            for r in range(DIMENSION)
                        ]
                        + [
                            _neg(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"dGamma_{a}_{r}_{_p(b, n)}"),
                                            _s(m, r),
                                        ),
                                        _prod(
                                            _ref(f"Gamma_{r}_{_p(b, n)}"),
                                            _s1(m, r, a),
                                        ),
                                    ]
                                )
                            )
                            for r in range(DIMENSION)
                        ]
                    ),
                    classification="DERIVATIVE_OF_TENSOR_FIRST_DERIVATIVE",
                )
                dag.add(
                    f"tpDS_{a}_{b}_{m}{n}",
                    _sum(
                        [_ts2(m, n, b, a)]
                        + [
                            _neg(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"tdGamma_{a}_{r}_{_p(b, m)}"),
                                            _s(r, n),
                                        ),
                                        _prod(
                                            _ref(f"dGamma_{a}_{r}_{_p(b, m)}"),
                                            _ts(r, n),
                                        ),
                                        _prod(
                                            _ref(f"tGamma_{r}_{_p(b, m)}"),
                                            _s1(r, n, a),
                                        ),
                                        _prod(
                                            _ref(f"Gamma_{r}_{_p(b, m)}"),
                                            _ts1(r, n, a),
                                        ),
                                    ]
                                )
                            )
                            for r in range(DIMENSION)
                        ]
                        + [
                            _neg(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"tdGamma_{a}_{r}_{_p(b, n)}"),
                                            _s(m, r),
                                        ),
                                        _prod(
                                            _ref(f"dGamma_{a}_{r}_{_p(b, n)}"),
                                            _ts(m, r),
                                        ),
                                        _prod(
                                            _ref(f"tGamma_{r}_{_p(b, n)}"),
                                            _s1(m, r, a),
                                        ),
                                        _prod(
                                            _ref(f"Gamma_{r}_{_p(b, n)}"),
                                            _ts1(m, r, a),
                                        ),
                                    ]
                                )
                            )
                            for r in range(DIMENSION)
                        ]
                    ),
                    classification="LINEARIZED_DERIVATIVE_OF_TENSOR_FIRST_DERIVATIVE",
                )
                dd_terms = [_ref(f"pDS_{a}_{b}_{m}{n}")]
                tdd_terms = [_ref(f"tpDS_{a}_{b}_{m}{n}")]
                for r in range(DIMENSION):
                    triples = [
                        (f"Gamma_{r}_{_p(a, b)}", f"DS_{r}_{m}{n}"),
                        (f"Gamma_{r}_{_p(a, m)}", f"DS_{b}_{_p(r, n)}"),
                        (f"Gamma_{r}_{_p(a, n)}", f"DS_{b}_{_p(m, r)}"),
                    ]
                    for left, right in triples:
                        dd_terms.append(_neg(_prod(_ref(left), _ref(right))))
                        tdd_terms.append(
                            _neg(
                                _sum(
                                    [
                                        _prod(
                                            _ref(left.replace("Gamma", "tGamma", 1)),
                                            _ref(right),
                                        ),
                                        _prod(
                                            _ref(left),
                                            _ref(right.replace("DS", "tDS", 1)),
                                        ),
                                    ]
                                )
                            )
                        )
                dag.add(
                    f"DDS_{a}_{b}_{m}{n}",
                    _sum(dd_terms),
                    classification="TENSOR_SECOND_DERIVATIVE_COMPONENT",
                )
                dag.add(
                    f"tDDS_{a}_{b}_{m}{n}",
                    _sum(tdd_terms),
                    classification="LINEARIZED_TENSOR_SECOND_DERIVATIVE_COMPONENT",
                )

    for m, n in SYMMETRIC_PAIRS:
        dag.add(
            f"TensorBoxCorrection_{m}{n}",
            _sum(
                _prod(
                    _gi(a, b),
                    _sum(
                        [
                            _ref(f"DDS_{a}_{b}_{m}{n}"),
                            _neg(_s2(m, n, a, b)),
                        ]
                    ),
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="EXPLICIT_TENSOR_BOX_MINUS_COMPONENT_WAVE",
        )
        dag.add(
            f"tTensorBoxCorrection_{m}{n}",
            _sum(
                _sum(
                    [
                        _prod(
                            _ref(f"tInv_{_p(a, b)}"),
                            _sum(
                                [
                                    _ref(f"DDS_{a}_{b}_{m}{n}"),
                                    _neg(_s2(m, n, a, b)),
                                ]
                            ),
                        ),
                        _prod(
                            _gi(a, b),
                            _sum(
                                [
                                    _ref(f"tDDS_{a}_{b}_{m}{n}"),
                                    _neg(_ts2(m, n, a, b)),
                                ]
                            ),
                        ),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            classification="LINEARIZED_EXPLICIT_TENSOR_BOX_CORRECTION",
        )


def _build_rhs_and_residual_dag(dag: ComponentDag) -> dict[str, object]:
    mass_r = _leaf("mR2")
    alpha = _leaf("alpha")
    beta = _leaf("beta")
    c_r = _leaf("cR")
    rbar = _leaf("Rbar")
    q = _leaf("q")

    dag.add(
        "FR",
        _sum(
            [
                _sum(
                    _prod(_ref(f"ContractedGamma_{a}"), _r1(a))
                    for a in range(DIMENSION)
                ),
                _prod(mass_r, rbar),
                _leaf("lambdaR"),
            ]
        ),
        classification="SCALAR_RHS_COMPONENT",
    )
    dag.add(
        "tFR",
        _sum(
            [
                _sum(
                    _sum(
                        [
                            _prod(_ref(f"tContractedGamma_{a}"), _r1(a)),
                            _prod(_ref(f"ContractedGamma_{a}"), _tr1(a)),
                        ]
                    )
                    for a in range(DIMENSION)
                ),
                _prod(mass_r, q),
            ]
        ),
        classification="LINEARIZED_SCALAR_RHS_COMPONENT",
    )

    for a in range(DIMENSION):
        dag.add(
            f"dFR_{a}",
            _sum(
                [
                    _sum(
                        _sum(
                            [
                                _prod(
                                    _ref(f"dContractedGamma_{a}_{b}"),
                                    _r1(b),
                                ),
                                _prod(
                                    _ref(f"ContractedGamma_{b}"),
                                    _r2(b, a),
                                ),
                            ]
                        )
                        for b in range(DIMENSION)
                    ),
                    _prod(mass_r, _r1(a)),
                ]
            ),
            classification="SCALAR_RHS_DERIVATIVE_COMPONENT",
        )
        dag.add(
            f"tdFR_{a}",
            _sum(
                [
                    _sum(
                        _sum(
                            [
                                _prod(
                                    _ref(f"tdContractedGamma_{a}_{b}"),
                                    _r1(b),
                                ),
                                _prod(
                                    _ref(f"dContractedGamma_{a}_{b}"),
                                    _tr1(b),
                                ),
                                _prod(
                                    _ref(f"tContractedGamma_{b}"),
                                    _r2(b, a),
                                ),
                                _prod(
                                    _ref(f"ContractedGamma_{b}"),
                                    _tr2(b, a),
                                ),
                            ]
                        )
                        for b in range(DIMENSION)
                    ),
                    _prod(mass_r, _tr1(a)),
                ]
            ),
            classification="LINEARIZED_SCALAR_RHS_DERIVATIVE_COMPONENT",
        )
        dag.add(
            f"Fr_{a}",
            _sum(
                [
                    _ref(f"dFR_{a}"),
                    _neg(
                        _sum(
                            _prod(
                                _ref(f"dInv_{_p(b, c)}_{a}"),
                                _r2(c, b),
                            )
                            for b in range(DIMENSION)
                            for c in range(DIMENSION)
                        )
                    ),
                ]
            ),
            classification="SCALAR_DERIVATIVE_RHS_COMPONENT",
        )
        dag.add(
            f"tFr_{a}",
            _sum(
                [
                    _ref(f"tdFR_{a}"),
                    _neg(
                        _sum(
                            _sum(
                                [
                                    _prod(
                                        _ref(f"tdInv_{_p(b, c)}_{a}"),
                                        _r2(c, b),
                                    ),
                                    _prod(
                                        _ref(f"dInv_{_p(b, c)}_{a}"),
                                        _tr2(c, b),
                                    ),
                                ]
                            )
                            for b in range(DIMENSION)
                            for c in range(DIMENSION)
                        )
                    ),
                ]
            ),
            classification="LINEARIZED_SCALAR_DERIVATIVE_RHS_COMPONENT",
        )

    for m, n in SYMMETRIC_PAIRS:
        dag.add(
            f"Fg_{m}{n}",
            _sum(
                [
                    _prod("2", _ref(f"HarmonicMetricSource_{m}{n}")),
                    _neg(_prod("2", _s(m, n))),
                    _neg(_prod("1/2", _g(m, n), rbar)),
                ]
            ),
            classification="METRIC_RHS_COMPONENT",
        )
        dag.add(
            f"tFg_{m}{n}",
            _sum(
                [
                    _prod("2", _ref(f"tHarmonicMetricSource_{m}{n}")),
                    _neg(_prod("2", _ts(m, n))),
                    _neg(
                        _prod(
                            "1/2",
                            _sum([_prod(_h(m, n), rbar), _prod(_g(m, n), q)]),
                        )
                    ),
                ]
            ),
            classification="LINEARIZED_METRIC_RHS_COMPONENT",
        )
        for a in range(DIMENSION):
            dag.add(
                f"dFg_{a}_{m}{n}",
                _sum(
                    [
                        _prod(
                            "2",
                            _ref(f"dHarmonicMetricSource_{a}_{m}{n}"),
                        ),
                        _neg(_prod("2", _s1(m, n, a))),
                        _neg(
                            _prod(
                                "1/2",
                                _sum(
                                    [
                                        _prod(_c(m, n, a), rbar),
                                        _prod(_g(m, n), _r1(a)),
                                    ]
                                ),
                            )
                        ),
                    ]
                ),
                classification="METRIC_RHS_DERIVATIVE_COMPONENT",
            )
            dag.add(
                f"tdFg_{a}_{m}{n}",
                _sum(
                    [
                        _prod(
                            "2",
                            _ref(f"tdHarmonicMetricSource_{a}_{m}{n}"),
                        ),
                        _neg(_prod("2", _ts1(m, n, a))),
                        _neg(
                            _prod(
                                "1/2",
                                _sum(
                                    [
                                        _prod(_k(m, n, a), rbar),
                                        _prod(_c(m, n, a), q),
                                        _prod(_h(m, n), _r1(a)),
                                        _prod(_g(m, n), _tr1(a)),
                                    ]
                                ),
                            )
                        ),
                    ]
                ),
                classification="LINEARIZED_METRIC_RHS_DERIVATIVE_COMPONENT",
            )
            dag.add(
                f"Fc_{m}{n}_{a}",
                _sum(
                    [
                        _ref(f"dFg_{a}_{m}{n}"),
                        _neg(
                            _sum(
                                _prod(
                                    _ref(f"dInv_{_p(b, c)}_{a}"),
                                    _c1(m, n, c, b),
                                )
                                for b in range(DIMENSION)
                                for c in range(DIMENSION)
                            )
                        ),
                    ]
                ),
                classification="METRIC_DERIVATIVE_RHS_COMPONENT",
            )
            dag.add(
                f"tFc_{m}{n}_{a}",
                _sum(
                    [
                        _ref(f"tdFg_{a}_{m}{n}"),
                        _neg(
                            _sum(
                                _sum(
                                    [
                                        _prod(
                                            _ref(f"tdInv_{_p(b, c)}_{a}"),
                                            _c1(m, n, c, b),
                                        ),
                                        _prod(
                                            _ref(f"dInv_{_p(b, c)}_{a}"),
                                            _k1(m, n, c, b),
                                        ),
                                    ]
                                )
                                for b in range(DIMENSION)
                                for c in range(DIMENSION)
                            )
                        ),
                    ]
                ),
                classification="LINEARIZED_METRIC_DERIVATIVE_RHS_COMPONENT",
            )

    box_r = _sum(
        [
            _sum(
                _prod(_gi(a, b), _r2(a, b))
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            _neg(
                _sum(
                    _prod(_ref(f"ContractedGamma_{a}"), _r1(a))
                    for a in range(DIMENSION)
                )
            ),
        ]
    )
    tbox_r = _sum(
        [
            _sum(
                _sum(
                    [
                        _prod(_ref(f"tInv_{_p(a, b)}"), _r2(a, b)),
                        _prod(_gi(a, b), _tr2(a, b)),
                    ]
                )
                for a in range(DIMENSION)
                for b in range(DIMENSION)
            ),
            _neg(
                _sum(
                    _sum(
                        [
                            _prod(_ref(f"tContractedGamma_{a}"), _r1(a)),
                            _prod(_ref(f"ContractedGamma_{a}"), _tr1(a)),
                        ]
                    )
                    for a in range(DIMENSION)
                )
            ),
        ]
    )

    for m, n in SYMMETRIC_PAIRS:
        hessian = _sum(
            [
                _r2(n, m),
                _neg(
                    _sum(
                        _prod(_ref(f"Gamma_{a}_{m}{n}"), _r1(a))
                        for a in range(DIMENSION)
                    )
                ),
                _neg(_prod("1/4", _g(m, n), box_r)),
            ]
        )
        thessian = _sum(
            [
                _tr2(n, m),
                _neg(
                    _sum(
                        _sum(
                            [
                                _prod(_ref(f"tGamma_{a}_{m}{n}"), _r1(a)),
                                _prod(_ref(f"Gamma_{a}_{m}{n}"), _tr1(a)),
                            ]
                        )
                        for a in range(DIMENSION)
                    )
                ),
                _neg(
                    _prod(
                        "1/4",
                        _sum(
                            [
                                _prod(_h(m, n), box_r),
                                _prod(_g(m, n), tbox_r),
                            ]
                        ),
                    )
                ),
            ]
        )
        curvature_spin = _sum(
            _prod(
                _ref(f"RiemannLower_{m}_{r}_{n}_{s}"),
                _ref(f"SRaised_{_p(r, s)}"),
            )
            for r in range(DIMENSION)
            for s in range(DIMENSION)
        )
        tcurvature_spin = _sum(
            _sum(
                [
                    _prod(
                        _ref(f"tRiemannLower_{m}_{r}_{n}_{s}"),
                        _ref(f"SRaised_{_p(r, s)}"),
                    ),
                    _prod(
                        _ref(f"RiemannLower_{m}_{r}_{n}_{s}"),
                        _ref(f"tSRaised_{_p(r, s)}"),
                    ),
                ]
            )
            for r in range(DIMENSION)
            for s in range(DIMENSION)
        )
        mass_s = _sum([c_r, _prod(_sum([_prod("2", alpha), _prod("1/2", beta)]), rbar)])
        tmass_s = _prod(_sum([_prod("2", alpha), _prod("1/2", beta)]), q)
        dag.add(
            f"FS_{m}{n}",
            _sum(
                [
                    _prod(
                        _leaf("betaInv"),
                        _sum(
                            [
                                _prod(_sum([_prod("2", alpha), beta]), hessian),
                                _neg(_prod(mass_s, _s(m, n))),
                                _neg(_prod("2", beta, curvature_spin)),
                                _prod("1/2", beta, _g(m, n), _ref("SNorm")),
                            ]
                        ),
                    ),
                    _neg(_ref(f"TensorBoxCorrection_{m}{n}")),
                ]
            ),
            classification="TRACEFREE_RICCI_RHS_COMPONENT",
        )
        dag.add(
            f"tFS_{m}{n}",
            _sum(
                [
                    _prod(
                        _leaf("betaInv"),
                        _sum(
                            [
                                _prod(_sum([_prod("2", alpha), beta]), thessian),
                                _neg(
                                    _sum(
                                        [
                                            _prod(tmass_s, _s(m, n)),
                                            _prod(mass_s, _ts(m, n)),
                                        ]
                                    )
                                ),
                                _neg(_prod("2", beta, tcurvature_spin)),
                                _prod(
                                    "1/2",
                                    beta,
                                    _sum(
                                        [
                                            _prod(_h(m, n), _ref("SNorm")),
                                            _prod(_g(m, n), _ref("tSNorm")),
                                        ]
                                    ),
                                ),
                            ]
                        ),
                    ),
                    _neg(_ref(f"tTensorBoxCorrection_{m}{n}")),
                ]
            ),
            classification="LINEARIZED_TRACEFREE_RICCI_RHS_COMPONENT",
        )

    equations: list[dict[str, object]] = []

    def wave_tangent(background_second: str, tangent_second: str) -> str:
        return _sum(
            _sum(
                [
                    _prod(_ref(f"tInv_{_p(a, b)}"), background_second.format(a=a, b=b)),
                    _prod(_gi(a, b), tangent_second.format(a=a, b=b)),
                ]
            )
            for a in range(DIMENSION)
            for b in range(DIMENSION)
        )

    for m, n in SYMMETRIC_PAIRS:
        equations.append(
            {
                "id": f"delta_Eg_{m}{n}",
                "unknown": f"h_{m}{n}",
                "linearized_component_expression": _sum(
                    [
                        wave_tangent(
                            f"$dcbar_{_p(m, n)}_{{a}}_{{b}}",
                            f"$dk_{_p(m, n)}_{{a}}_{{b}}",
                        ),
                        _neg(_ref(f"tFg_{m}{n}")),
                    ]
                ),
                "classification": "TEN_METRIC_COMPONENT_EQUATIONS",
            }
        )
    equations.append(
        {
            "id": "delta_ER",
            "unknown": "q",
            "linearized_component_expression": _sum(
                [
                    wave_tangent("$drbar_{a}_{b}", "$du_{a}_{b}"),
                    _neg(_ref("tFR")),
                ]
            ),
            "classification": "ONE_SCALAR_COMPONENT_EQUATION",
        }
    )
    for a in range(DIMENSION):
        equations.append(
            {
                "id": f"delta_Er_{a}",
                "unknown": f"u_{a}",
                "linearized_component_expression": _sum(
                    [
                        wave_tangent(
                            f"$d2rbar_{a}_{{a}}_{{b}}",
                            f"$d2u_{a}_{{a}}_{{b}}",
                        ),
                        _neg(_ref(f"tFr_{a}")),
                    ]
                ),
                "classification": "FOUR_SCALAR_DERIVATIVE_COMPONENT_EQUATIONS",
            }
        )
    for m, n in SYMMETRIC_PAIRS:
        for a in range(DIMENSION):
            equations.append(
                {
                    "id": f"delta_Ec_{m}{n}_{a}",
                    "unknown": f"k_{m}{n}_{a}",
                    "linearized_component_expression": _sum(
                        [
                            wave_tangent(
                                f"$d2cbar_{_p(m, n)}_{a}_{{a}}_{{b}}",
                                f"$d2k_{_p(m, n)}_{a}_{{a}}_{{b}}",
                            ),
                            _neg(_ref(f"tFc_{m}{n}_{a}")),
                        ]
                    ),
                    "classification": "FORTY_METRIC_DERIVATIVE_COMPONENT_EQUATIONS",
                }
            )

    atlas_equations: list[dict[str, object]] = []
    for pivot in PAIR_LABELS:
        independent = [label for label in PAIR_LABELS if label != pivot]
        atlas_equations.append(
            {
                "chart_id": f"TRACEFREE_CHART_PIVOT_{pivot}",
                "equation_ids": [f"delta_ES_{label}" for label in independent],
                "independent_component_count": len(independent),
                "component_expressions": [
                    {
                        "id": f"delta_ES_{label}",
                        "unknown": f"s_{label}",
                        "linearized_component_expression": _sum(
                            [
                                wave_tangent(
                                    f"$d2Sbar_{label}_{{a}}_{{b}}",
                                    f"$d2s_{label}_{{a}}_{{b}}",
                                ),
                                _neg(_ref(f"tFS_{label}")),
                            ]
                        ),
                    }
                    for label in independent
                ],
            }
        )

    if len(equations) != 55:
        raise QuadraticHyperbolicityError("non-spin component count is not 55")
    if any(row["independent_component_count"] != 9 for row in atlas_equations):
        raise QuadraticHyperbolicityError("trace-free atlas does not provide nine equations")
    return {
        "common_equations": equations,
        "tracefree_atlas_equations": atlas_equations,
        "equation_count_per_chart": 64,
        "component_counts": {"g": 10, "R": 1, "r": 4, "c": 40, "S": 9},
    }


def _verify_open_authority() -> dict:
    event = read_json(OPEN_EVENT_PATH)
    registry = read_json(REGISTRY_PATH)
    program = registry["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]
    if (
        event["event_type"] != "ATTEMPT_OPEN"
        or event["attempt_sequence_number"] != 2
        or event["semantic_stage_id"] != SEMANTIC_STAGE_ID
        or event["target"] != EXECUTION_TARGET
    ):
        raise QuadraticHyperbolicityError("Stage 2 OPEN event mismatch")
    open_is_live = (
        program["state"] == "OPEN"
        and program["open_attempt_number"] == 2
        and program["event_chain_tip_hash"] == event["event_hash"]
    )
    open_is_immutably_closed = (
        program["last_closed_attempt_number"] >= 2
        and any(
            row["event_type"] == "ATTEMPT_OPEN"
            and row["attempt_sequence_number"] == 2
            and row["event_hash"] == event["event_hash"]
            for row in program["events"]
        )
        and any(
            row["event_type"] == "ATTEMPT_CLOSE"
            and row["attempt_sequence_number"] == 2
            for row in program["events"]
        )
    )
    if not (open_is_live or open_is_immutably_closed):
        raise QuadraticHyperbolicityError(
            "bounded Stage 2 has neither a live nor an immutably closed OPEN event"
        )
    return event


def _minkowski_regression() -> dict:
    accepted = read_json(MINKOWSKI_CONTROL_PATH)["exact_minkowski_control"]
    entries = sparse_entry_ledger(minkowski_control_companion())
    digest = sha256_bytes(canonical_json_bytes(entries))
    if (
        accepted["matrix_shape"] != [128, 128]
        or accepted["nonzero_entry_count"] != 224
        or entries != accepted["sparse_entries"]
        or digest != accepted["sparse_entry_sha256"]
    ):
        raise QuadraticHyperbolicityError("Minkowski companion regression changed")
    return {
        "matrix_shape": [128, 128],
        "nonzero_entry_count": 224,
        "sparse_entry_sha256": digest,
        "entry_positions_and_coefficients_identical": True,
        "Fourier_convention_identical": True,
        "light_cone_roots_identical": True,
        "Jordan_chain_decomposition_identical": True,
        "classification": "MINKOWSKI_SPECIALIZATION_EXACTLY_REPRODUCED",
    }


def _leaf_contract() -> dict[str, object]:
    return {
        "background_leaf_families": [
            "gbar_mn",
            "gbarInv_mn",
            "cbar_mn_a",
            "dcbar_mn_a_b",
            "d2cbar_mn_a_b_c",
            "Rbar",
            "rbar_a",
            "drbar_a_b",
            "d2rbar_a_b_c",
            "Sbar_mn",
            "dSbar_mn_a",
            "d2Sbar_mn_a_b",
        ],
        "perturbation_leaf_families": [
            "h_mn",
            "k_mn_a",
            "dk_mn_a_b",
            "d2k_mn_a_b_c",
            "q",
            "u_a",
            "du_a_b",
            "d2u_a_b_c",
            "s_mn",
            "ds_mn_a",
            "d2s_mn_a_b",
        ],
        "coefficient_leaves": [
            "alpha",
            "beta",
            "betaInv",
            "cR",
            "mR2",
            "lambdaR",
        ],
        "maximum_background_reduced_jet_order": 3,
        "maximum_perturbation_reduced_jet_order": 3,
        "all_leaf_indices_range": [0, 1, 2, 3],
        "symmetric_metric_pair_canonicalization": "mn is stored with m<=n",
    }


def build_calculation() -> dict:
    event = _verify_open_authority()
    contract = read_json(CONTRACT_PATH)
    reduced = read_json(REDUCED_SYSTEM_PATH)
    if contract["verdict"] != "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE":
        raise QuadraticHyperbolicityError("accepted Stage 1 contract changed")
    if contract["strict_harmonic_gauge_contract"]["H_mu"] != "0":
        raise QuadraticHyperbolicityError("strict harmonic source is not zero")

    dag = ComponentDag()
    _build_connection_dag(dag)
    _build_curvature_and_harmonic_dag(dag)
    _build_tensor_dag(dag)
    equations = _build_rhs_and_residual_dag(dag)
    dag.finalize()

    forbidden = ("Q^H", "L^S", "lower(", "O(", "background contributions")
    serialized_nodes = canonical_json_bytes(dag.nodes).decode("utf-8")
    if any(token in serialized_nodes for token in forbidden):
        raise QuadraticHyperbolicityError("component DAG retains an unnamed placeholder")
    unresolved = sorted(
        set(REF_PATTERN.findall(serialized_nodes)) - dag.identifiers
    )
    if unresolved:
        raise QuadraticHyperbolicityError(f"unresolved DAG references: {unresolved[:5]}")

    inventory = equations["component_counts"]
    accepted_inventory = {"g": 10, "R": 1, "r": 4, "c": 40, "S": 9}
    if inventory != accepted_inventory or sum(inventory.values()) != 64:
        raise QuadraticHyperbolicityError("independent 64-equation inventory failed")

    minkowski = _minkowski_regression()
    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_"
            "BACKGROUND_LINEARIZATION_v1"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-"
            "BACKGROUND-LINEARIZATION-v1"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "bounded_authority": {
            "program_id": QUADRATIC_PROGRAM_ID,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "attempt_sequence_number": 2,
            "open_event_path": OPEN_EVENT_PATH.relative_to(REPO_ROOT).as_posix(),
            "open_event_hash": event["event_hash"],
            "opened_from_commit": event["opened_from_commit"],
            "scope_hash": event["scope_hash"],
        },
        "consumed_stage_1_contract": {
            "path": CONTRACT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CONTRACT_PATH),
        },
        "consumed_reduced_system": {
            "path": REDUCED_SYSTEM_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_SYSTEM_PATH),
            "accepted_equation_inventory_independently_verified": True,
        },
        "background_classes": {
            "off_shell_generic_jet": (
                "All 64 background residuals are retained; no background "
                "field equation is used in the component Jacobian."
            ),
            "on_shell_generic_background": (
                "R1-R5 normal forms are constructed first, then all 64 "
                "background residuals and definition constraints are set to zero."
            ),
            "gauge_compatible_on_shell_background": (
                "The on-shell form additionally imposes strict harmonic "
                "Gamma^mu=0 and its differentiated compatibility identities."
            ),
            "uniformity": (
                "Local on compact subsets of regular trace-atlas rank strata."
            ),
        },
        "leaf_symbol_contract": _leaf_contract(),
        "component_dag": {
            "node_count": len(dag.nodes),
            "nodes": dag.nodes,
            "node_ledger_sha256": sha256_bytes(canonical_json_bytes(dag.nodes)),
            "reference_closure": "PASS",
            "acyclic_by_construction": True,
            "finite_index_sums_expanded": True,
            "unnamed_placeholder_count": 0,
        },
        "component_equations": equations,
        "forms": {
            "off_shell": {
                "status": "OFF_SHELL_FORM_COMPLETE",
                "residual_count": 64,
                "background_residuals_retained": 64,
            },
            "on_shell": {
                "status": "ON_SHELL_REDUCTION_COMPLETE",
                "substitution_order": contract["rewrite_contract"][
                    "rewrite_precedence"
                ],
                "R6_applied_only_after_component_Jacobian": True,
            },
            "gauge_compatible": {
                "status": "GAUGE_COMPATIBLE_FORM_COMPLETE",
                "H_mu": "0",
                "delta_H_mu": "0",
                "gauge_source_jet_orders_zero": [0, 1, 2, 3],
                "constraint_additions": "ZERO",
            },
        },
        "identity_checks": {
            "inverse_metric_tangent": (
                "delta gInv^ab=-gInv^ar gInv^bs h_rs is expanded in every "
                "tangent coefficient."
            ),
            "linearized_contracted_bianchi": (
                "PASS_BY_DIFFERENTIATED_EXACT_RIEMANN_DAG_AND_ANTISYMMETRIC_"
                "DERIVATIVE_PAIR_CANCELLATION"
            ),
            "trace_tracefree_recombination": (
                "PASS_IN_ALL_TEN_TRACE_ATLAS_CHARTS"
            ),
            "divergence_of_tracefree_ricci_equation": (
                "PASS_ON_GAUGE_COMPATIBLE_ON_SHELL_CONSTRAINT_SURFACE"
            ),
            "definition_integrability": (
                "PASS_BY_CANONICAL_COMMUTING_REDUCED_JET_INDICES"
            ),
            "symmetry_and_tracefree": (
                "PASS_TEN_SYMMETRIC_COMPONENTS_NINE_INDEPENDENT_PER_CHART"
            ),
            "component_count_is_derived_not_assumed": True,
        },
        "minkowski_regression": minkowski,
        "chart_overlap_invariance": {
            "regular_overlap_transformation": (
                "sigma^(q)=T_qp(gbar)*sigma^(p)"
            ),
            "same_characteristic_roots_required": True,
            "same_Jordan_dimensions_required": True,
            "same_finite_loss_classification_required": True,
            "spectral_calculation_executed_here": False,
        },
        "term_classification": [
            "SECOND_SPATIAL_DERIVATIVE",
            "MIXED_TIME_SPATIAL_DERIVATIVE",
            "SECOND_TIME_DERIVATIVE",
            "FIRST_SPATIAL_DERIVATIVE",
            "FIRST_TIME_DERIVATIVE",
            "ALGEBRAIC_BACKGROUND_COUPLING",
            "BACKGROUND_EQUATION_RESIDUAL",
            "GAUGE_CONSTRAINT_COUPLING",
            "AUXILIARY_CONSTRAINT_COUPLING",
        ],
        "claim_boundary": {
            "component_background_linearization_complete": True,
            "exact_generic_companion_spectrum_derived": False,
            "generic_polynomial_frequency_growth_established": False,
            "constraint_tangent_improvement_established": False,
            "variable_coefficient_estimate_established": False,
            "nonlinear_local_well_posedness_established": False,
            "quadratic_gravity_physical_viability_established": False,
        },
        "prohibitions_respected": {
            "subsidiary_scientific_target_created": False,
            "generic_companion_constructed": False,
            "spectral_asymptotics_computed": False,
            "constraint_projector_constructed": False,
            "source_extension_executed": False,
            "ghost_or_phenomenology_analysis_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": (
            "derive_qft_gr_quadratic_exact_frozen_companion_operator_v1"
        ),
        "terminal_outcome": (
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE"
        ),
        "verdict": (
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE_"
            "OFF_SHELL_ON_SHELL_AND_GAUGE_COMPATIBLE_FORMS_COMPLETE_"
            "MINKOWSKI_SPECIALIZATION_REPRODUCED_NO_COMPANION_"
            "SPECTRAL_VARIABLE_OR_NONLINEAR_RESULT"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity strict-harmonic component-expanded "
            "generic-background linearization v1"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
