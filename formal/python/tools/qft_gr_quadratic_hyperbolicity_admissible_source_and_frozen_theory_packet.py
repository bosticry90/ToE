from __future__ import annotations

import hashlib
import subprocess

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


SELECTION_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
    "SELECTION_RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_20260728_v0.json"
)
CURRENT_TARGET = (
    "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_"
    "and_frozen_theory_packet_v0"
)
REVIEW_TARGET = (
    "review_qft_gr_quadratic_hyperbolicity_admissible_source_"
    "and_frozen_theory_packet_v0_result"
)
PRESERVED_COMMIT = "e785b98d"
PRESERVED_PATH = (
    "formal/science_capsules/"
    "qft_gr_full_higher_derivative_constraint_set_initial_data_v0/"
    "derivation/full_higher_derivative_constraint_set_initial_data_domain.md"
)
PRESERVED_BLOB_OID = "4351a53e0a582f5ccdd23d6aa80ee5372bda9e6f"
PRESERVED_BLOB_SIZE = 5818
PRESERVED_BLOB_SHA256 = (
    "2a3a3af211ab2c82ceb72e0c8505d3558954d1e14a5d187180b59250b637fb16"
)


def _read_preserved_blob() -> bytes:
    tree = subprocess.run(
        ["git", "ls-tree", "-r", PRESERVED_COMMIT, "--", PRESERVED_PATH],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if not tree or PRESERVED_BLOB_OID not in tree:
        raise QuadraticHyperbolicityError("preserved candidate blob identity drift")
    blob = subprocess.run(
        ["git", "cat-file", "blob", PRESERVED_BLOB_OID],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    if len(blob) != PRESERVED_BLOB_SIZE:
        raise QuadraticHyperbolicityError("preserved candidate blob size drift")
    if hashlib.sha256(blob).hexdigest() != PRESERVED_BLOB_SHA256:
        raise QuadraticHyperbolicityError("preserved candidate blob hash drift")
    return blob


def build_packet() -> dict:
    selection_review = read_json(SELECTION_REVIEW_PATH)
    if selection_review["accepted"] is not True:
        raise QuadraticHyperbolicityError("bounded reconciliation was not accepted")
    if selection_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError("source-packet authority mismatch")
    _read_preserved_blob()
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
            "FROZEN_THEORY_PACKET_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "preparation_target": CURRENT_TARGET,
        "consumed_selection_review": {
            "path": SELECTION_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(SELECTION_REVIEW_PATH),
            "selected_route": selection_review["selected_route"],
        },
        "admissible_primary_sources": [
            {
                "source_id": "ARXIV_2607_11879_V1",
                "title": (
                    "Higher-derivative gravitational effective field theories "
                    "are generically weakly hyperbolic"
                ),
                "authors": [
                    "Farid Thaalba",
                    "Fernando Abalos",
                    "Miguel Bezares",
                ],
                "submitted": "2026-07-13",
                "url": "https://arxiv.org/abs/2607.11879",
                "role": "PRIMARY_CURRENT_PHYSICAL_PRINCIPAL_BLOCK_REFERENCE",
                "claim_boundary": (
                    "Independently reproduce the quadratic physical spin-2 "
                    "pencil and its defective repeated roots; do not import "
                    "the source conclusion as the ToE result."
                ),
                "locators": [
                    "equations 25-28",
                    "physical spin-2 block discussion",
                    "discussion of adapted norms and derivative loss",
                ],
            },
            {
                "source_id": "ARXIV_1811_07869_V4",
                "title": "About the Cauchy problem in Stelle's quadratic gravity",
                "authors": [
                    "J. Osorio Morales",
                    "O. P. Santillan",
                ],
                "url": "https://arxiv.org/abs/1811.07869",
                "role": "HISTORICAL_SMOOTH_EXISTENCE_COMPARATOR",
                "claim_boundary": (
                    "Use the harmonic/auxiliary formulation and C-infinity "
                    "existence results as a comparator. Do not treat its "
                    "Proposition 9 continuous-dependence statement, identified "
                    "there as a conjecture, as an established Sobolev estimate."
                ),
                "locators": [
                    "Theorem 1",
                    "Theorem 2",
                    "Proposition 9 (Conjecture)",
                ],
            },
            {
                "source_id": "NOAKES_1983_JMP_24_1846",
                "title": (
                    "The initial value formulation of higher derivative gravity"
                ),
                "author": "David R. Noakes",
                "journal": "Journal of Mathematical Physics 24, 1846 (1983)",
                "doi": "10.1063/1.525906",
                "url": (
                    "https://pubs.aip.org/aip/jmp/article/24/7/1846/226302/"
                    "The-initial-value-formulation-of-higher-derivative"
                ),
                "role": "HISTORICAL_HARMONIC_REDUCTION_COMPARATOR",
                "claim_boundary": (
                    "Use as historical formulation context, not as a substitute "
                    "for a same-order uniform symmetrizer."
                ),
            },
            {
                "source_id": "ARXIV_2407_08775_V1",
                "title": (
                    "Well-posed initial value formulation of general effective "
                    "field theories of gravity"
                ),
                "authors": [
                    "Pau Figueras",
                    "Aaron Held",
                    "Áron D. Kovács",
                ],
                "url": "https://arxiv.org/abs/2407.08775",
                "role": "EXCLUDED_REGULARIZED_FORMULATION_COMPARATOR",
                "claim_boundary": (
                    "Regularizing terms and fiducial massive modes are outside "
                    "the frozen unregularized theory and cannot establish its "
                    "physical strong hyperbolicity."
                ),
            },
        ],
        "preserved_candidate_input": {
            "classification": "PRESERVED_NOT_ADOPTED",
            "commit": PRESERVED_COMMIT,
            "path": PRESERVED_PATH,
            "git_blob_oid": PRESERVED_BLOB_OID,
            "byte_size": PRESERVED_BLOB_SIZE,
            "sha256": PRESERVED_BLOB_SHA256,
            "admissible_use": (
                "Candidate equations, conventions, and constraint inventory "
                "requiring independent rederivation and rebinding."
            ),
            "scientific_authority_conferred": False,
        },
        "frozen_theory": {
            "dimension": 4,
            "action_density": (
                "sqrt(-g) [c_R R + c_Lambda + alpha R^2 "
                "+ beta R_mn R^mn] + source"
            ),
            "coefficient_domains": {
                "G_principal": ["beta != 0", "3 alpha + beta != 0"],
                "G_Stelle": [
                    "beta != 0",
                    "3 alpha + beta != 0",
                    "c_R != 0",
                ],
                "spin2_obstruction_minimal_domain": ["beta != 0"],
            },
            "coefficient_mapping_to_arxiv_2607_11879": {
                "paper_alpha0": (
                    "ToE beta up to the overall nonzero action normalization"
                ),
                "paper_beta0": (
                    "-ToE alpha up to the overall nonzero action normalization"
                ),
                "principal_pencil_scaling": (
                    "Any nonzero constant multiple is equivalent for roots and "
                    "multiplicities."
                ),
            },
            "lower_order_at_fourth_order_principal_level": [
                "c_R R",
                "c_Lambda",
            ],
        },
        "frozen_conventions": {
            "metric_signature": "(-,+,+,+)",
            "riemann": (
                "R^rho_{ sigma mu nu} = partial_mu Gamma^rho_{nu sigma} "
                "- partial_nu Gamma^rho_{mu sigma} "
                "+ Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma} "
                "- Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma}"
            ),
            "ricci": "R_sigma_nu = R^rho_{ sigma rho nu}",
            "principal_covector": (
                "ell_mu = lambda n_mu + k_mu with n.n=-1, k.k=1, n.k=0"
            ),
            "physical_subspace": (
                "Two transverse-traceless spin-2 polarizations orthogonal "
                "to n and k."
            ),
            "box_symbol": "g^mu_nu ell_mu ell_nu = 1-lambda^2",
        },
        "source_scope": {
            "phase_a": "VACUUM",
            "first_extension": (
                "Prescribed smooth conserved T_mn with no new fourth-order "
                "metric or matter derivatives."
            ),
            "dynamical_hyperbolic_matter": "LATER_SEPARATE_PACKET",
            "semiclassical_nonlocal_or_state_dependent_source": (
                "EXCLUDED_UNTIL_SEPARATE_SOURCE_ADMISSIBILITY_REVIEW"
            ),
        },
        "phase_a_authorized_calculation": {
            "target": "derive_qft_gr_quadratic_physical_spin2_principal_block_v0",
            "required_outputs": [
                "Fourth-order physical transverse-traceless principal block.",
                "Matrix pencil for arbitrary nonzero spatial covector.",
                "Algebraic and geometric multiplicities at lambda = +/-1.",
                "Strong- and symmetric-hyperbolicity conclusions.",
                "Gauge/constraint invariance boundary of the physical block.",
                "Coefficient-stratum controls.",
            ],
        },
        "not_yet_authorized": [
            "Nonlinear auxiliary/harmonic formulation execution.",
            "Standard Sobolev energy estimate execution.",
            "Adapted derivative-loss energy estimate execution.",
            "Source extension.",
            "Maxwell-Dirac secondary calculation.",
        ],
        "prohibitions": [
            "No perturbative order reduction presented as the frozen theory.",
            "No artificial dissipation used as a continuum proof.",
            "No regulator field counted as an original physical mode.",
            "No fiducial massive mode used to claim unregularized hyperbolicity.",
            "No symmetry-reduced result used as generic 3+1 proof.",
            "No numerical stability substituted for a principal-symbol proof.",
            "No smooth existence result labeled strong hyperbolicity without a uniform symmetrizer.",
            "No Yukawa execution or rerun.",
        ],
        "selected_next_target": REVIEW_TARGET,
        "verdict": (
            "FROZEN_VACUUM_THEORY_AND_ADMISSIBLE_SOURCES_PREPARED_"
            "FOR_INDEPENDENT_REVIEW"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_packet,
        description=(
            "quadratic hyperbolicity admissible-source and frozen-theory packet"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
