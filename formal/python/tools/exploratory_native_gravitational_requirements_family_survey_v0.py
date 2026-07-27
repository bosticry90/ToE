from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_review_v0 as review,
)
from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_v0 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_20260718_v0.json"
)
HUMAN_SURVEY_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_exploratory_native_gravitational_requirements_family_survey_v0.py"
)
TARGET = "conduct_exploratory_native_gravitational_requirements_family_survey_v0"
VERDICT = "COMPLETED_NONAUTHORITATIVE_OPPORTUNITY_MAP_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_exploratory_native_gravitational_requirements_family_survey_v0_result"
)
MODE = "MANUAL_EXPLORATORY_NONAUTHORITATIVE"
ADJUDICATOR_ID = "CODEX_MANUAL_EXPLORATORY_SURVEY_20260718"

ACCEPTED_REVIEW_HASHES = {
    "formal/docs/lanes/EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_PACKET_REVIEW_20260718_v0.md":
        "2fd17a03cd7f53aea1e278675aca827c98c8a8c1ee30adbf90944e15e39c2e4a",
    review.REPORT_RELATIVE_PATH:
        "a58991c81c2047ef242d13e7cfad0e4e195d09a2c166015b2729428b2515f498",
    "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_packet_review_v0.py":
        "2c7327e8695c53527cceea9ba1c28f5b5d430f7aa7415c54074bb0216d6f34bc",
    "formal/python/tests/test_exploratory_native_gravitational_requirements_family_survey_packet_review_v0.py":
        "c7e009d8a553c4562609ebd0908243d4a4537db992fed9697a43513ba3f0eb2b",
    "formal/toe_formal/ToeFormal/Derivation/ExploratoryNativeGravitationalRequirementsFamilySurveyPacketReviewV0.lean":
        "8c907da3819f91a9af43e19ce8ed32db2b02c7d7870b1fddd4fec3f9287b0bf3",
}

SOURCE_CATALOG: dict[str, dict[str, Any]] = {
    "P1_MINIMAL_CONTRACT": {
        "title": "Minimal native continuum gravitational-sector contract",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json",
    },
    "P2_CK_STATUS": {
        "title": "Ck-family status synthesis",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json",
    },
    "P3_STRESS_POLICY": {
        "title": "Native stress-energy definition policy result review",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json",
    },
    "P4_MATTER_PACKET": {
        "title": "QFT/GR matter-field candidate packet",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json",
    },
    "P5_DISCRETE_POISSON": {
        "title": "Discrete weak-field Poisson structural theorem",
        "source_kind": "PROJECT_FORMAL_SURFACE",
        "reference": "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean",
    },
    "P6_0I_BLOCK": {
        "title": "Gravitomagnetic recovery packet review",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json",
    },
    "P7_STABILITY_OBLIGATION": {
        "title": "Native gravitational-principle response selection",
        "source_kind": "PROJECT_AUTHORITY",
        "reference": "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json",
    },
    "E1_IYER_WALD_1994": {
        "title": "Some Properties of Noether Charge and a Proposal for Dynamical Black Hole Entropy",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/gr-qc/9403028",
    },
    "E2_BERRY_GAIR_2011": {
        "title": "Linearized f(R) Gravity: Gravitational Radiation and Solar System Tests",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/1104.0819",
    },
    "E3_CHIBA_2003": {
        "title": "1/R Gravity and Scalar-Tensor Gravity",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/astro-ph/0307338",
    },
    "E4_FARAONI_2006": {
        "title": "Matter instability in modified gravity",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/astro-ph/0610734",
    },
    "E5_DOLGOV_KAWASAKI_2003": {
        "title": "Can modified gravity explain accelerated cosmic expansion?",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/astro-ph/0307285",
    },
    "E6_STELLE_1978": {
        "title": "Classical Gravity with Higher Derivatives",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://doi.org/10.1007/BF00760427",
    },
    "E7_LINDBLAD_RODNIANSKI_2004": {
        "title": "Global Existence for the Einstein Vacuum Equations in Wave Coordinates",
        "source_kind": "PRIMARY_MATHEMATICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/math/0411109",
    },
    "E8_LOVELOCK_1971": {
        "title": "The Einstein Tensor and Its Generalizations",
        "source_kind": "PRIMARY_MATHEMATICAL_LITERATURE",
        "reference": "https://doi.org/10.1063/1.1665613",
    },
    "E9_CAPOZZIELLO_STABILE_TROISI_2007": {
        "title": "Newtonian limit of f(R) gravity",
        "source_kind": "PRIMARY_THEORETICAL_LITERATURE",
        "reference": "https://arxiv.org/abs/0708.0723",
    },
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in ACCEPTED_REVIEW_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"accepted exploratory-survey review drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    accepted = _load_json(review.REPORT_RELATIVE_PATH)
    if accepted.get("verdict") != review.VERDICT:
        raise ValueError("exploratory-survey packet review was not accepted")
    if accepted.get("selected_next_target") != TARGET:
        raise ValueError("accepted review did not authorize this survey")
    if accepted["authorized_execution"].get("execution_count") != 1:
        raise ValueError("survey execution-count authorization mismatch")
    if accepted["scope"].get("real_matrix_cells_computed") != 0:
        raise ValueError("accepted review already contains real matrix cells")
    return rows


def _pointer(
    source_id: str,
    basis_type: str,
    pointer_role: str,
    scope_note: str,
) -> dict[str, Any]:
    if source_id not in SOURCE_CATALOG:
        raise ValueError(f"unknown survey source: {source_id}")
    return {
        "basis_type": basis_type,
        "pointer_role": pointer_role,
        "reference": source_id,
        "scope_note": scope_note,
    }


def _cell(
    requirement_id: str,
    family_id: str,
    label: str,
    rationale: str,
    assumptions: list[str],
    pointers: list[dict[str, Any]],
    uncertainty: str,
    resolving_work: str,
    priority: str = "DECISION_CRITICAL",
) -> dict[str, Any]:
    row = packet._blank_cell(requirement_id, family_id)
    row.update({
        "workflow_state": "SURVEYED_PROVISIONAL",
        "provisional_classification": label,
        "concise_rationale": rationale,
        "assumptions_and_domain": assumptions,
        "source_or_derivation_pointers": pointers,
        "main_uncertainty": uncertainty,
        "resolving_calculation_or_theorem": resolving_work,
        "priority_role": priority,
        "manual_adjudicator_id": ADJUDICATOR_ID,
        "manual_review_status": "PENDING_INDEPENDENT_RESULT_REVIEW",
    })
    if review.structural_entry_disposition(row) != "VALID_PROVISIONAL_ENTRY":
        raise ValueError(f"incomplete provisional cell: {row['cell_id']}")
    return row


def _surveyed_cells() -> list[dict[str, Any]]:
    p1 = lambda note: _pointer(
        "P1_MINIMAL_CONTRACT", "DIRECT_MATHEMATICAL_REASONING",
        "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", note,
    )
    iyer = lambda note: _pointer(
        "E1_IYER_WALD_1994", "ESTABLISHED_LITERATURE",
        "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", note,
    )
    return [
        _cell("R4_DIFF_COVARIANCE", "F_EH", "CLEARLY COMPATIBLE",
              "The Einstein-Hilbert integrand is a diffeomorphism scalar density.",
              ["Local four-dimensional metric action", "Constant scalar couplings"],
              [p1("Binds R4 and the frozen local metric scope."), iyer("Supports the general covariant-Lagrangian/Noether structure, not viability.")],
              "Covariance alone does not establish source coupling, stability, or recovery.",
              "No R4-only calculation is needed; derive a shared Noether identity only with R7."),
        _cell("R4_DIFF_COVARIANCE", "F_FR", "CLEARLY COMPATIBLE",
              "A metric f(R) integrand is covariant when f is a scalar function of R.",
              ["Metric formalism", "Local scalar f(R)", "Purely linear representative excluded"],
              [p1("Binds R4."), iyer("Applies to covariant metric Lagrangians; it does not cover every model property.")],
              "This limited symmetry result does not generalize a special f(R) model's viability.",
              "No R4-only work; retain model-specific questions for R8-R10."),
        _cell("R4_DIFF_COVARIANCE", "F_QUADRATIC", "CLEARLY COMPATIBLE",
              "Local contractions of quadratic curvature invariants are diffeomorphism scalars.",
              ["Metric formalism", "Covariant local curvature invariants", "Constant coefficients"],
              [p1("Binds R4."), iyer("Supports only the common diffeomorphism-invariant structure.")],
              "The statement does not establish equivalence among different invariants or stability.",
              "No R4-only work; compare spectrum and source response under R9-R10."),

        _cell("R5_CK_FIREWALL", "F_EH", "LIKELY COMPATIBLE",
              "The comparator can be written with no Ck embedding, multiplier, or variation.",
              ["No hidden Ck-dependent coupling in the comparison action"],
              [_pointer("P2_CK_STATUS", "DIRECT_MATHEMATICAL_REASONING", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Makes Ck admissibility-only and supplies no action embedding.")],
              "A later project embedding could introduce a hidden Ck-dependent coefficient.",
              "Audit any future embedding; an explicit seam-to-action map would be needed for selection."),
        _cell("R5_CK_FIREWALL", "F_FR", "LIKELY COMPATIBLE",
              "Curvature nonlinearity does not by itself require a Ck action embedding.",
              ["The frozen f(R) comparator has no Ck-dependent coefficients"],
              [_pointer("P2_CK_STATUS", "DIRECT_MATHEMATICAL_REASONING", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Architecture-only Ck rule; no f(R)-specific statement.")],
              "No accepted source proves that every future project f(R) embedding remains Ck-independent.",
              "Require an explicit Ck-to-curvature map before treating R5 as discriminating."),
        _cell("R5_CK_FIREWALL", "F_QUADRATIC", "LIKELY COMPATIBLE",
              "Quadratic curvature invariants do not by themselves require Ck embedding or variation.",
              ["The frozen quadratic comparator has constant, Ck-independent coefficients"],
              [_pointer("P2_CK_STATUS", "DIRECT_MATHEMATICAL_REASONING", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Architecture-only Ck rule; no quadratic-action selection.")],
              "Future coefficient construction could create a Ck dependence not present in the comparator.",
              "Require an accepted seam-to-coefficient law or counterexample before selection."),

        _cell("R7_SOURCE_COMPATIBILITY", "F_EH", "LIKELY COMPATIBLE",
              "Covariant matter variation and the diffeomorphism identity support on-shell source conservation.",
              ["Diffeomorphism-invariant matter action", "Matter equations hold", "No anomalous external source"],
              [_pointer("P3_STRESS_POLICY", "DIRECT_MATHEMATICAL_REASONING", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Fixes the project stress-energy definition policy but does not derive it from a selected action."), iyer("Supports the relevant Noether structure.")],
              "The project has not executed a native continuum matter variation coupled to this family.",
              "Derive the shared metric-matter Ward identity with all equations and boundary terms explicit."),
        _cell("R7_SOURCE_COMPATIBILITY", "F_FR", "LIKELY COMPATIBLE",
              "A covariant metric f(R) action can use the same variational matter source and on-shell identity.",
              ["Metric f(R)", "Explicitly covariant matter coupling", "Matter equations hold"],
              [_pointer("P4_MATTER_PACKET", "EXPERT_JUDGMENT", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Records matter candidates but not a family-wide gravitational coupling derivation."), iyer("General covariant-Lagrangian identity only.")],
              "Nonminimal couplings and family-wide matter choices can change the bookkeeping.",
              "Derive the identity for one bounded f(R) representative and the frozen matter representative."),
        _cell("R7_SOURCE_COMPATIBILITY", "F_QUADRATIC", "LIKELY COMPATIBLE",
              "Higher derivatives do not remove the generalized diffeomorphism identity for a covariant metric action.",
              ["Covariant local quadratic metric action", "Covariant matter action", "Compact-support bulk variation"],
              [iyer("Supports generalized Noether identities, not a complete source-coupling proof.")],
              "Exact boundary terms, field-equation order, and matter coupling remain unspecified.",
              "Derive a shared quadratic metric-matter Ward identity in the bounded representative."),

        _cell("R8_NEWTON_POISSON", "F_EH", "CLEARLY COMPATIBLE",
              "The zero-Lambda Einstein-Hilbert standard comparator has the Newton-Poisson weak-field limit.",
              ["Minkowski background", "Zero or locally negligible cosmological term", "Standard source normalization"],
              [_pointer("P5_DISCRETE_POISSON", "DIRECT_MATHEMATICAL_REASONING", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Project theorem is discrete and structural, not a continuum EH derivation."), _pointer("E9_CAPOZZIELLO_STABILE_TROISI_2007", "KNOWN_COMPARATOR_BEHAVIOR", "SUPPLIED_STANDARD_PHYSICS_COMPARATOR_ONLY", "Used only to orient the standard comparator against modified weak-field potentials.")],
              "This is supplied comparator behavior and does not establish native ToE recovery or every Lambda choice.",
              "Reproduce it as the alpha=beta=0 control in the shared linearized 00 derivation."),
        _cell("R8_NEWTON_POISSON", "F_FR", "UNRESOLVED",
              "Analytic representatives can yield Newtonian plus scalar/Yukawa response and can approximate GR in restricted regimes.",
              ["Analytic metric f(R) near a Minkowski background", "Conserved weak source", "No whole-family inference from one f"],
              [_pointer("E2_BERRY_GAIR_2011", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Covers analytic linearized representatives and an extra scalar response."), _pointer("E9_CAPOZZIELLO_STABILE_TROISI_2007", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Shows parameter- and regime-dependent Newtonian potentials; not all f(R).")],
              "Mass scale, boundary conditions, analytic form, and coefficient choices vary across the family.",
              "Derive the source-normalized 00 Green function for R+alpha R^2 as a bounded representative."),
        _cell("R8_NEWTON_POISSON", "F_QUADRATIC", "UNRESOLVED",
              "Generic representatives produce Newtonian plus massive-mode corrections, so exact no-fit recovery is coefficient-dependent.",
              ["Local metric R+alpha R^2+beta Ricci^2 representative", "Minkowski background", "Conserved stationary source"],
              [_pointer("E6_STELLE_1978", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Supports generic massive modes and Yukawa-corrected static response in the stated representative.")],
              "Special coefficient ratios, source normalization, and boundary conditions prevent a whole-family label.",
              "Derive the shared 00 Green function and state which recovery requires a limit or fitted range."),

        _cell("R9_MOMENTUM_CURRENT", "F_EH", "CLEARLY COMPATIBLE",
              "Standard linearized Einstein gravity has a stationary momentum-current response.",
              ["Linearized GR about Minkowski", "Conserved stationary source", "Shared gauge and normalization"],
              [_pointer("P6_0I_BLOCK", "KNOWN_COMPARATOR_BEHAVIOR", "PROJECT_AUTHORITY_REQUIREMENT_SOURCE", "Records that the project has not derived the continuum 0i equation; comparator behavior remains supplied.")],
              "No native tensor equation or project 0i derivation exists.",
              "Recover the EH response as the alpha=beta=0 control of the shared 0i derivation."),
        _cell("R9_MOMENTUM_CURRENT", "F_FR", "UNRESOLVED",
              "Simple analytic f(R) representatives add a scalar, but no whole-family stationary 0i result was established.",
              ["Analytic metric f(R) about Minkowski", "Conserved stationary T_0i", "No generalization beyond cited representatives"],
              [_pointer("E2_BERRY_GAIR_2011", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Establishes the extra scalar in an analytic linearized class, not a full stationary 0i theorem."), _pointer("E3_CHIBA_2003", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Supports scalar-tensor representation in its domain; not a family-wide 0i calculation.")],
              "Gauge conventions, scalar/vector decomposition, and nonanalytic models remain open.",
              "Derive the conserved-source 0i Green function for the beta=0 representative."),
        _cell("R9_MOMENTUM_CURRENT", "F_QUADRATIC", "UNRESOLVED",
              "The additional massive spin-2 sector can modify momentum-current transport independently of the scalar 00 response.",
              ["Generic local quadratic representative about Minkowski", "Conserved stationary source"],
              [_pointer("E6_STELLE_1978", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Supports the massive spin-2 content; the exact project 0i normalization remains to be derived.")],
              "Which poles couple to T_0i under the project conventions has not been calculated.",
              "Derive and decompose the stationary 0i Green function in the shared representative."),

        _cell("R10_STABILITY_NO_FIT", "F_EH", "LIKELY COMPATIBLE",
              "Small asymptotically flat perturbations of Minkowski have rigorous stability support in Einstein gravity.",
              ["Small-data asymptotically flat vacuum or stated Einstein-matter domain", "Near-Minkowski background"],
              [_pointer("E7_LINDBLAD_RODNIANSKI_2004", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Limited to its small-data wave-coordinate theorem domain.")],
              "This does not cover all backgrounds, cosmological terms, matter choices, or the full no-fit obligation.",
              "Use EH as the pole/residue and weak-field control, without upgrading limited stability to a universal claim."),
        _cell("R10_STABILITY_NO_FIT", "F_FR", "UNRESOLVED",
              "Metric f(R) contains both stable and unstable model sectors, so no whole-family stability label is justified.",
              ["Metric f(R)", "Model- and background-specific stability analysis", "No extrapolation from one model"],
              [_pointer("E4_FARAONI_2006", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Gives stability conditions and exclusions in a stated class."), _pointer("E5_DOLGOV_KAWASAKI_2003", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Concrete instability counterexample only.")],
              "Tachyon, matter, nonlinear, and phenomenological stability are distinct obligations.",
              "Compute scalar pole mass/residue and state stability inequalities for the bounded beta=0 representative."),
        _cell("R10_STABILITY_NO_FIT", "F_QUADRATIC", "LIKELY INCOMPATIBLE",
              "Generic standard-sign quadratic gravity contains a negative-energy or negative-residue massive spin-2 excitation.",
              ["Local metric quadratic representative", "Minkowski linearization", "Ordinary propagator interpretation", "Generic beta not zero"],
              [_pointer("E6_STELLE_1978", "ESTABLISHED_LITERATURE", "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE", "Supports the generic massive spin-2 instability concern and special-ratio caveats.")],
              "Degenerate coefficients, nonstandard quantization, and other assumption changes prevent a blanket whole-family theorem.",
              "Compute poles and residues and prove or refute removal of the bad spin-2 pole without changing stated assumptions."),

        _cell("R2_METRIC_ONLY", "F_EXTRA_FIELD", "OUTSIDE FROZEN SCOPE",
              "The family contains an additional fundamental gravitational scalar, vector, or tensor.",
              ["R2 is applied as a frozen survey-envelope filter, not a physical no-go"],
              [p1("Defines the metric-only envelope.")],
              "No physical assessment of extra-field gravity was attempted.",
              "Revisit only under fresh authority that relaxes R2.", "CONTEXTUAL"),
        _cell("R2_METRIC_ONLY", "F_CONNECTION_TORSION", "OUTSIDE FROZEN SCOPE",
              "An independent connection or torsion violates the frozen metric-only field-content envelope.",
              ["R2 is a scope filter", "No judgment of physical viability"],
              [p1("Defines the metric-only envelope.")],
              "Palatini and torsion subclasses were not surveyed.",
              "Revisit only under fresh authority that relaxes the field-content envelope.", "CONTEXTUAL"),
        _cell("R3_LOCALITY", "F_NONLOCAL", "OUTSIDE FROZEN SCOPE",
              "The family is explicitly nonlocal while R3 freezes a local scalar-density envelope.",
              ["R3 is a scope filter", "No judgment of physical viability"],
              [p1("Defines the local action envelope.")],
              "No nonlocal kernel or effective-local expansion was assessed.",
              "Revisit only under fresh authority that relaxes locality.", "CONTEXTUAL"),
        _cell("R6_LOCAL_VARIATION", "F_EQUIVALENCE_PROBE", "CLEARLY COMPATIBLE",
              "Exact boundary or four-dimensional topological variants can preserve compact-support local bulk variation.",
              ["Smooth fields", "Compactly supported bulk metric variation", "Exact algebraic, boundary, or topological relation"],
              [p1("Defines the compact-support local-bulk domain."), iyer("Supports boundary-sensitive covariant variational structure; no real-family merge is inferred.")],
              "Boundary observables, global charges, matter coupling, modes, and stability are not transported automatically.",
              "For every future equivalence claim, prove preservation separately for each property and domain.", "CONTEXTUAL"),
    ]


def _question_rows() -> list[dict[str, Any]]:
    def ids(req: str, families: list[str]) -> list[str]:
        return [f"EXP_{req}__{family}" for family in families]

    primary = ["F_EH", "F_FR", "F_QUADRATIC"]
    return [
        {
            "question_id": "DQ1_DIFF_COVARIANCE_DISCRIMINATION",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether R4 distinguishes the three primary local metric families.",
            "provisional_answer": "No obvious discrimination: all three admit covariant scalar-density actions.",
            "assumptions": ["Frozen local metric representatives", "Constant scalar couplings"],
            "reasoning_basis_types": ["DIRECT_MATHEMATICAL_REASONING", "ESTABLISHED_LITERATURE"],
            "source_ids": ["P1_MINIMAL_CONTRACT", "E1_IYER_WALD_1994"],
            "uncertainty": "Covariance alone does not decide coupling, modes, recovery, or stability.",
            "resolving_work": "No R4-only derivation; derive the shared Noether identity with R7.",
            "supporting_cell_ids": ids("R4_DIFF_COVARIANCE", primary),
            "priority_rank": 7,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ2_CK_FIREWALL_ACTION_RELEVANCE",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether R5 fixes curvature dependence or controls only project architecture.",
            "provisional_answer": "Architecture only on current authority; no Ck-to-action map was found.",
            "assumptions": ["No hidden Ck-dependent comparator coefficients"],
            "reasoning_basis_types": ["DIRECT_MATHEMATICAL_REASONING"],
            "source_ids": ["P2_CK_STATUS"],
            "uncertainty": "A future accepted seam law could create action leverage.",
            "resolving_work": "Supply an accepted seam-to-Lagrangian map or a discriminating counterexample.",
            "supporting_cell_ids": ids("R5_CK_FIREWALL", primary),
            "priority_rank": 5,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ3_SOURCE_COMPATIBILITY_DISCRIMINATION",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether R7 distinguishes primary metric families after matter coupling is explicit.",
            "provisional_answer": "Probably not by itself under ordinary covariant on-shell matter coupling.",
            "assumptions": ["Covariant matter action", "Matter equations hold", "No anomalous external source"],
            "reasoning_basis_types": ["DIRECT_MATHEMATICAL_REASONING", "ESTABLISHED_LITERATURE"],
            "source_ids": ["P3_STRESS_POLICY", "P4_MATTER_PACKET", "E1_IYER_WALD_1994"],
            "uncertainty": "The project has policy, not a native continuum matter variation tied to a selected action.",
            "resolving_work": "Derive a shared metric-matter diffeomorphism Ward identity.",
            "supporting_cell_ids": ids("R7_SOURCE_COMPATIBILITY", primary),
            "priority_rank": 6,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ4_NEWTONIAN_RECOVERY_DISCRIMINATION",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether exact Newton-Poisson recovery separates nonlinear and quadratic curvature from EH without tuning.",
            "provisional_answer": "Existence of a Newtonian regime is probably nonselective; exact no-fit recovery may discriminate.",
            "assumptions": ["Stationary weak field about Minkowski", "Shared source normalization", "No whole-family extrapolation"],
            "reasoning_basis_types": ["KNOWN_COMPARATOR_BEHAVIOR", "ESTABLISHED_LITERATURE"],
            "source_ids": ["P5_DISCRETE_POISSON", "E2_BERRY_GAIR_2011", "E6_STELLE_1978", "E9_CAPOZZIELLO_STABILE_TROISI_2007"],
            "uncertainty": "Masses, coefficients, boundary conditions, and analytic form vary across families.",
            "resolving_work": "Derive the shared source-normalized stationary 00 Green function.",
            "supporting_cell_ids": ids("R8_NEWTON_POISSON", primary),
            "priority_rank": 2,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ5_MOMENTUM_CURRENT_INDEPENDENCE",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether stationary 0i momentum-current response adds information beyond the 00 sector.",
            "provisional_answer": "Provisionally yes; 0i probes propagating spin content not fixed by a scalar/static limit.",
            "assumptions": ["Minkowski linearization", "Conserved stationary source", "Shared gauge conventions"],
            "reasoning_basis_types": ["DIRECT_MATHEMATICAL_REASONING", "ESTABLISHED_LITERATURE"],
            "source_ids": ["P6_0I_BLOCK", "E2_BERRY_GAIR_2011", "E3_CHIBA_2003", "E6_STELLE_1978"],
            "uncertainty": "No native continuum 0i equation or common family calculation exists.",
            "resolving_work": "Derive the stationary conserved-source 0i Green function and its coupled poles.",
            "supporting_cell_ids": ids("R8_NEWTON_POISSON", primary) + ids("R9_MOMENTUM_CURRENT", primary),
            "priority_rank": 1,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ6_STABILITY_NO_FIT_DISCRIMINATION",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Which precise R10 calculation has the greatest family-discriminating power.",
            "provisional_answer": "Pole, residue, and stability analysis has the strongest visible leverage.",
            "assumptions": ["Local metric theories near Minkowski", "Ordinary propagator interpretation", "No observational coefficient fitting"],
            "reasoning_basis_types": ["ESTABLISHED_LITERATURE", "DIRECT_MATHEMATICAL_REASONING"],
            "source_ids": ["E4_FARAONI_2006", "E5_DOLGOV_KAWASAKI_2003", "E6_STELLE_1978", "E7_LINDBLAD_RODNIANSKI_2004"],
            "uncertainty": "Linear, nonlinear, matter, and phenomenological stability are distinct.",
            "resolving_work": "Compute poles, residues, and tachyon/ghost conditions for the bounded alpha-beta representative.",
            "supporting_cell_ids": ids("R10_STABILITY_NO_FIT", primary),
            "priority_rank": 3,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ7_NATIVE_SEAM_LAGRANGIAN_CONSTRAINT",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Whether accepted ToE-specific commitments constrain the gravitational Lagrangian.",
            "provisional_answer": "None was found; current seam/admissibility rules do not select curvature dependence.",
            "assumptions": ["Only accepted source-bound project commitments count", "Method rules are not physical postulates"],
            "reasoning_basis_types": ["EXPERT_JUDGMENT", "DIRECT_MATHEMATICAL_REASONING"],
            "source_ids": ["P1_MINIMAL_CONTRACT", "P2_CK_STATUS", "P3_STRESS_POLICY", "P5_DISCRETE_POISSON", "P6_0I_BLOCK"],
            "uncertainty": "This is an authority-surface absence finding, not proof that no principle can be formulated.",
            "resolving_work": "After the shared derivation, test whether an accepted cross-pillar law fixes derivative order, poles, or coupling.",
            "supporting_cell_ids": ids("R5_CK_FIREWALL", primary) + ids("R7_SOURCE_COMPATIBILITY", primary),
            "priority_rank": 4,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
        {
            "question_id": "DQ8_PROPERTY_SCOPED_EQUIVALENCE",
            "status": "ANSWERED_PROVISIONAL",
            "issue": "Which properties may be transported across a boundary, algebraic, or topological relation.",
            "provisional_answer": "Only the exact proved property; compact-support local bulk equivalence does not transport global or physical properties automatically.",
            "assumptions": ["Smooth fields", "Exact identity or proved boundary/topological relation", "Frozen compact-support bulk domain"],
            "reasoning_basis_types": ["DIRECT_MATHEMATICAL_REASONING", "ESTABLISHED_LITERATURE"],
            "source_ids": ["P1_MINIMAL_CONTRACT", "E1_IYER_WALD_1994"],
            "uncertainty": "No real-family property-transport proof or merge is asserted.",
            "resolving_work": "Require transformation, domain, inverse, boundary conditions, and property-by-property proof for each future claim.",
            "supporting_cell_ids": ["EXP_R6_LOCAL_VARIATION__F_EQUIVALENCE_PROBE"],
            "priority_rank": 8,
            "authority": "EXPLORATORY_NONAUTHORITATIVE",
        },
    ]


def _forms() -> list[dict[str, Any]]:
    surveyed = {row["cell_id"]: row for row in _surveyed_cells()}
    if len(surveyed) != 22:
        raise ValueError("surveyed-cell count or identity collision")
    return [surveyed.get(row["cell_id"], copy.deepcopy(row)) for row in packet._blank_survey_forms()]


def _controls(forms: list[dict[str, Any]], questions: list[dict[str, Any]]) -> dict[str, Any]:
    dispositions = [review.structural_entry_disposition(row) for row in forms]
    surveyed_ids = {
        row["cell_id"] for row in forms if row["workflow_state"] == "SURVEYED_PROVISIONAL"
    }
    question_support = {
        cell_id for question in questions for cell_id in question["supporting_cell_ids"]
    }
    contextual_ids = {
        "EXP_R2_METRIC_ONLY__F_EXTRA_FIELD",
        "EXP_R2_METRIC_ONLY__F_CONNECTION_TORSION",
        "EXP_R3_LOCALITY__F_NONLOCAL",
    }
    label_tally = {
        label: sum(row["provisional_classification"] == label for row in forms)
        for label in packet.PERMITTED_PROVISIONAL_LABELS
    }
    referenced_sources = {
        pointer["reference"]
        for row in forms
        for pointer in row["source_or_derivation_pointers"]
    } | {source_id for question in questions for source_id in question["source_ids"]}
    rows = [
        {"control_id": "CTRL_AUTHORIZED_ONCE_AND_REVIEW_ACCEPTED", "passed": True},
        {"control_id": "CTRL_EIGHT_QUESTIONS_ANSWERED_PROVISIONALLY", "passed": len(questions) == 8 and all(row["status"] == "ANSWERED_PROVISIONAL" for row in questions)},
        {"control_id": "CTRL_EXACT_22_SURVEYED_AND_48_NOT_SURVEYED", "passed": dispositions.count("VALID_PROVISIONAL_ENTRY") == 22 and dispositions.count("VALID_NOT_SURVEYED") == 48 and "INCOMPLETE_SURVEY_ENTRY" not in dispositions},
        {"control_id": "CTRL_DESCRIPTIVE_LABEL_TALLY", "passed": label_tally == {"CLEARLY COMPATIBLE": 6, "LIKELY COMPATIBLE": 7, "LIKELY INCOMPATIBLE": 1, "CLEARLY INCOMPATIBLE": 0, "UNRESOLVED": 5, "OUTSIDE FROZEN SCOPE": 3}},
        {"control_id": "CTRL_ALL_REFERENCED_SOURCES_DECLARED", "passed": referenced_sources.issubset(SOURCE_CATALOG)},
        {"control_id": "CTRL_ONLY_QUESTION_SUPPORT_OR_EXPLICIT_CONTEXT_CELLS_SURVEYED", "passed": surveyed_ids == question_support | contextual_ids},
        {"control_id": "CTRL_NO_V2_CELL_OR_SELECTOR_FIELDS", "passed": all(not {"cell_status", "evidence_id", "claim_scope", "survivor_set", "equivalence_class", "scientific_outcome"}.intersection(row) for row in forms)},
        {"control_id": "CTRL_NEXT_STEP_IS_REVIEW_NOT_SCIENTIFIC_EXECUTION", "passed": SELECTED_NEXT_TARGET == "review_exploratory_native_gravitational_requirements_family_survey_v0_result"},
    ]
    return {
        "control_count": len(rows),
        "pass_count": sum(row["passed"] for row in rows),
        "failure_count": sum(not row["passed"] for row in rows),
        "rows": rows,
        "structural_disposition_tally": {
            status: dispositions.count(status)
            for status in ("VALID_PROVISIONAL_ENTRY", "VALID_NOT_SURVEYED", "INCOMPLETE_SURVEY_ENTRY")
        },
        "descriptive_label_tally": label_tally,
    }


def build_survey() -> dict[str, Any]:
    authority_rows = _validate_authority()
    forms = _forms()
    questions = _question_rows()
    controls = _controls(forms, questions)
    if controls["control_count"] != controls["pass_count"]:
        failed = [row["control_id"] for row in controls["rows"] if not row["passed"]]
        raise ValueError(f"exploratory survey control failure: {failed}")

    human = REPO_ROOT / HUMAN_SURVEY_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("survey human record or focused test missing")
    source_rows = [
        {"source_id": source_id, **metadata}
        for source_id, metadata in SOURCE_CATALOG.items()
    ]
    not_surveyed = [
        row["cell_id"] for row in forms if row["workflow_state"] == "NOT_SURVEYED"
    ]
    return {
        "schema_id": "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "mode": MODE,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_EXPLORATORY_SURVEY_RESULT_REVIEW_ONLY",
        "authority": {
            "accepted_packet_review_verdict": review.VERDICT,
            "authorized_execution_count": 1,
            "execution_consumed_count": 1,
            "frozen_review_inputs": authority_rows,
            "human_survey": {"relative_path": HUMAN_SURVEY_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "claim_boundary": {
            "exploratory": True,
            "nonauthoritative": True,
            "manual_judgment_visible": True,
            "labels_are_research_judgments_only": True,
            "labels_map_to_V2_statuses": False,
            "V2_population_permitted": False,
            "automated_selector_present": False,
            "authoritative_family_judgments_made": False,
            "native_principle_identified": False,
            "gravitational_action_selected_or_proposed": False,
            "metric_variation_executed": False,
            "frame_dragging_reopened": False,
        },
        "source_register": {
            "source_count": len(source_rows),
            "retrieval_date": "2026-07-18",
            "rows": source_rows,
            "custody_confers_scientific_relevance": False,
            "special_case_generalizes_to_family": False,
        },
        "decision_critical_question_register": {
            "question_count": 8,
            "answered_question_count": 8,
            "rows": questions,
        },
        "survey_form_contract": {
            "possible_relationship_count": 70,
            "surveyed_provisional_count": 22,
            "not_surveyed_count": 48,
            "incomplete_entry_count": 0,
            "forms": forms,
            "explicit_NOT_SURVEYED_cell_ids": not_surveyed,
        },
        "opportunity_map": {
            "broadly_nonselective_hypotheses": [
                "R4 among the three primary metric-local families",
                "R5 while it remains an architecture/admissibility firewall only",
                "R7 under ordinary covariant on-shell matter coupling",
                "R8 if it requires only existence of some Newtonian regime",
            ],
            "scope_filters_not_dynamics_selectors": ["R1", "R2", "R3", "R6"],
            "probable_discriminators": [
                "R9 stationary momentum-current response",
                "R10 separated pole, residue, and stability obligations",
            ],
            "supplied_assumption_dependency": {
                "observation": "Second-order equations or no extra modes would strongly narrow the primary envelope.",
                "native_project_principle": False,
                "source_ids": ["E8_LOVELOCK_1971", "E2_BERRY_GAIR_2011", "E6_STELLE_1978"],
            },
            "native_discriminator_found": False,
            "native_discriminator_absence_scope": "No accepted seam-to-Lagrangian map was found in the frozen sources; this is not a proof of impossibility.",
            "dependency_hypotheses": [
                "R4 and R7 are linked by Noether identities, but R7 also carries matter-source content.",
                "R8 and R9 remain independent until derived from one shared tensor equation and convention.",
                "R5 becomes selective only if an accepted seam law maps admissibility to an action property.",
                "R10 must be split into spectrum, linear stability, nonlinear stability, recovery, and no-fit obligations.",
            ],
            "highest_value_next_bounded_derivation": {
                "comparison_instrument": "S = integral sqrt(-g) [R + alpha R^2 + beta R_mn R^mn] + S_m",
                "tasks": [
                    "derive the conserved-source linearized propagator or equivalent equations",
                    "derive stationary 00 and 0i Green functions under one convention",
                    "list poles, residues, and propagating modes",
                    "display alpha=beta=0, beta=0, and generic beta!=0 cases",
                    "state every limiting regime or coefficient choice needed for recovery",
                ],
                "question_ids_addressed": [
                    "DQ4_NEWTONIAN_RECOVERY_DISCRIMINATION",
                    "DQ5_MOMENTUM_CURRENT_INDEPENDENCE",
                    "DQ6_STABILITY_NO_FIT_DISCRIMINATION",
                ],
                "project_action_proposal": False,
                "authority": "EXPLORATORY_RECOMMENDATION_ONLY",
            },
            "best_bounded_no_go_or_counterexample_test": {
                "conjecture": "For generic beta!=0 under ordinary local metric kinetic assumptions, the negative-residue massive spin-2 pole cannot be removed while retaining the intended local source response except through an explicit degeneracy, limit, or assumption change.",
                "theorem_established": False,
                "authority": "EXPLORATORY_TEST_RECOMMENDATION_ONLY",
            },
            "future_postulate_leverage_locations": [
                "derivative order",
                "propagating pole content",
                "gravitational source coupling",
                "accepted cross-sector dynamical relation",
            ],
            "deferred_without_current_leverage_loss": [
                "remaining 48 cells",
                "physics inside out-of-envelope families",
                "global and boundary equivalence observables",
                "observational coefficient fitting",
                "matter-sector choice",
                "metric variation of a selected action",
                "frame-dragging recovery",
            ],
        },
        "result_controls": controls,
        "scope": {
            "manual_exploratory_survey_executed": True,
            "decision_critical_questions_answered": 8,
            "provisional_survey_cells_completed": 22,
            "NOT_SURVEYED_cells_retained": 48,
            "authoritative_V2_matrix_cells_computed": 0,
            "authoritative_family_judgments_made": False,
            "real_family_equivalence_established": False,
            "authoritative_survivor_computation_executed": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_selected_or_proposed": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "tensor_field_equation_derived": False,
            "frame_dragging_reopened": False,
            "automated_action_selection_lane_reopened": False,
            "automatic_V3_authorized": False,
        },
        "current_posture": {
            "exploratory_survey_contract": "ACCEPTED_8_OF_8_GATES",
            "manual_exploratory_survey": VERDICT,
            "surveyed_provisional_cells": "22_OF_70",
            "NOT_SURVEYED_cells": "48_OF_70",
            "decision_critical_questions": "8_ANSWERED_PROVISIONALLY",
            "authoritative_V2_matrix": "0_OF_70",
            "automated_action_selection_tooling": "CLOSED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "metric_variation": "NOT_EXECUTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_survey(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate or check the bounded manual exploratory gravity survey.")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("exploratory gravitational survey artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "questions_answered": 8,
            "surveyed_provisional_cells": 22,
            "not_surveyed_cells": 48,
            "authoritative_V2_cells": 0,
            "selected_next_target": SELECTED_NEXT_TARGET,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
