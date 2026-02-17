from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
	p = start.resolve()
	while p != p.parent:
		if (p / "formal").exists():
			return p
		p = p.parent
	raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "SR" / "CovarianceObjectDischargeStub.lean"
TARGET_GATE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md"
TARGET_FULL_PATH = (
	REPO_ROOT
	/ "formal"
	/ "docs"
	/ "paper"
	/ "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
)


def _read(path: Path) -> str:
	assert path.exists(), f"Missing required file: {path}"
	return path.read_text(encoding="utf-8")


def _theorem_block(text: str, theorem_name: str) -> str:
	start_token = f"theorem {theorem_name}"
	start_idx = text.find(start_token)
	assert start_idx != -1, f"Missing theorem token in Lean file: {start_token}"

	next_markers = [
		text.find("\n\ntheorem ", start_idx + len(start_token)),
		text.find("\n\ndef ", start_idx + len(start_token)),
		text.find("\n\ninductive ", start_idx + len(start_token)),
		text.find("\n\nstructure ", start_idx + len(start_token)),
		text.find("\nend", start_idx + len(start_token)),
	]
	next_markers = [idx for idx in next_markers if idx != -1]
	end_idx = min(next_markers) if next_markers else len(text)
	return text[start_idx:end_idx]


def _assert_tokens_in_order(text: str, tokens: list[str], label: str) -> None:
	cursor = -1
	for token in tokens:
		idx = text.find(token, cursor + 1)
		assert idx != -1, f"Missing required token in {label}: {token}"
		assert idx > cursor, f"Token-order drift in {label}: {token}"
		cursor = idx


def test_sr_inevitability_substance_theorem_tokens_are_present() -> None:
	lean_text = _read(LEAN_PATH)
	required = [
		"structure SRInevitabilityMinimizedAssumptions_v0",
		"theorem sr_inevitability_necessity_under_minimized_assumptions_v0",
		"theorem sr_inevitability_counterfactual_breaks_without_required_assumption_v0",
		"theorem sr_inevitability_structural_classification_of_constructive_route_v0",
		"theorem sr_inevitability_discharge_ready_bundle_v0",
		"theorem sr_inevitability_route_bundle_without_shortcuts_v0",
		"theorem sr_inevitability_constructive_route_without_compatibility_wrappers_v0",
		"theorem sr_inevitability_positive_dependency_core_lemma_bundle_v0",
		"theorem sr_inevitability_physics_substance_dependency_bundle_v0",
		"theorem sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0",
		"theorem sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
	]
	missing = [tok for tok in required if tok not in lean_text]
	assert not missing, "Missing SR inevitability theorem token(s): " + ", ".join(missing)


def test_sr_constructive_route_theorem_body_is_wrapper_free() -> None:
	lean_text = _read(LEAN_PATH)
	block = _theorem_block(
		lean_text,
		"sr_inevitability_constructive_route_without_compatibility_wrappers_v0",
	)
	forbidden_wrapper_tokens = [
		"SR_COVARIANCE_PHASE6_INEVITABILITY_NECESSITY_COUNTERFACTUAL_DISCHARGE_COMPLETION_LOCK_v0",
		"SR_COVARIANCE_PHASE6_INEVITABILITY_THEOREM_DISCHARGE_CLOSURE_LOCK_v0",
		"srFullDerivationPhase6InevitabilityTheoremDischargeStatusTokenV0",
	]
	leaked = [tok for tok in forbidden_wrapper_tokens if tok in block]
	assert not leaked, "SR constructive-route theorem should be wrapper-free but contains: " + ", ".join(leaked)
	assert "sr_cycle28_covariance_contract_stub_token_v0 hMin.transform hMin.velocityCompose hMin.hInv" in block, (
		"SR constructive-route theorem must use direct covariance-contract dependency theorem."
	)


def test_sr_positive_dependency_theorem_calls_core_lemmas() -> None:
	lean_text = _read(LEAN_PATH)
	theorem_name = "sr_inevitability_positive_dependency_core_lemma_bundle_v0"
	block = _theorem_block(lean_text, theorem_name)
	required_core_calls = [
		"sr_inevitability_discharge_ready_bundle_v0 hMin",
		"sr_inevitability_constructive_route_without_compatibility_wrappers_v0 hMin",
		"sr_inevitability_route_bundle_without_shortcuts_v0 hMin",
	]
	missing = [tok for tok in required_core_calls if tok not in block]
	assert not missing, "SR positive-dependency theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_sr_physics_substance_dependency_theorem_calls_core_lemmas() -> None:
	lean_text = _read(LEAN_PATH)
	theorem_name = "sr_inevitability_physics_substance_dependency_bundle_v0"
	block = _theorem_block(lean_text, theorem_name)
	required_core_calls = [
		"sr_cycle28_interval_invariance_stub_token_v0 hMin.transform hMin.hInv",
		"sr_cycle28_covariance_contract_stub_token_v0 hMin.transform hMin.velocityCompose hMin.hInv",
		"sr_inevitability_positive_dependency_core_lemma_bundle_v0 hMin",
	]
	missing = [tok for tok in required_core_calls if tok not in block]
	assert not missing, "SR physics-substance theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_sr_endpoint_counterfactual_theorem_calls_interval_dependency() -> None:
	lean_text = _read(LEAN_PATH)
	theorem_name = "sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0"
	block = _theorem_block(lean_text, theorem_name)
	required_core_calls = [
		"sr_inevitability_physics_substance_dependency_bundle_v0 hMin",
	]
	missing = [tok for tok in required_core_calls if tok not in block]
	assert not missing, "SR endpoint-counterfactual theorem is missing required dependency calls: " + ", ".join(missing)


def test_sr_independent_necessity_class_theorem_uses_endpoint_counterfactual_route() -> None:
	lean_text = _read(LEAN_PATH)
	theorem_name = "sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0"
	block = _theorem_block(lean_text, theorem_name)
	required_core_calls = [
		"sr_inevitability_physics_substance_dependency_bundle_v0 hMin",
		"sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0 hMin hMissingInterval",
	]
	missing = [tok for tok in required_core_calls if tok not in block]
	assert not missing, "SR independent necessity-class theorem is missing required dependency calls: " + ", ".join(missing)

	forbidden_direct_restatement = [
		"sr_inevitability_necessity_under_minimized_assumptions_v0 hMin",
	]
	leaked = [tok for tok in forbidden_direct_restatement if tok in block]
	assert not leaked, "SR independent necessity-class theorem must not be a direct necessity restatement: " + ", ".join(leaked)


def test_sr_inevitability_gate_doc_is_pinned() -> None:
	text = _read(TARGET_GATE_PATH)
	required = [
		"Inevitability obligation linkage",
		"sr_inevitability_necessity_under_minimized_assumptions_v0",
		"sr_inevitability_counterfactual_breaks_without_required_assumption_v0",
		"sr_inevitability_structural_classification_of_constructive_route_v0",
		"sr_inevitability_discharge_ready_bundle_v0",
		"sr_inevitability_route_bundle_without_shortcuts_v0",
		"sr_inevitability_physics_substance_dependency_bundle_v0",
		"sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0",
		"sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
		"SRInevitabilityMinimizedAssumptions_v0",
		"SRInevitabilityCanonicalCovarianceRoute_v0",
		"SRInevitabilityIntervalInvariantRoute_v0",
		"SRInevitabilityNoShortcutRoute_v0",
		"SRInevitabilityClosureSurface_v0",
	]
	missing = [tok for tok in required if tok not in text]
	assert not missing, "Missing SR inevitability gate token(s): " + ", ".join(missing)


def test_sr_inevitability_obligation_tokens_synced_to_full_target() -> None:
	gate_text = _read(TARGET_GATE_PATH)
	full_text = _read(TARGET_FULL_PATH)

	obligation_tokens = [
		"sr_inevitability_necessity_under_minimized_assumptions_v0",
		"sr_inevitability_counterfactual_breaks_without_required_assumption_v0",
		"sr_inevitability_structural_classification_of_constructive_route_v0",
		"sr_inevitability_discharge_ready_bundle_v0",
		"sr_inevitability_route_bundle_without_shortcuts_v0",
		"sr_inevitability_physics_substance_dependency_bundle_v0",
		"sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0",
		"sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
		"SRInevitabilityMinimizedAssumptions_v0",
		"SRInevitabilityCanonicalCovarianceRoute_v0",
		"SRInevitabilityIntervalInvariantRoute_v0",
		"SRInevitabilityNoShortcutRoute_v0",
		"SRInevitabilityClosureSurface_v0",
	]

	missing_in_gate = [tok for tok in obligation_tokens if tok not in gate_text]
	missing_in_full = [tok for tok in obligation_tokens if tok not in full_text]
	assert not missing_in_gate, "SR inevitability obligation token(s) missing in gate target: " + ", ".join(missing_in_gate)
	assert not missing_in_full, "SR inevitability obligation token(s) missing in full target: " + ", ".join(missing_in_full)


def test_sr_inevitability_obligation_token_order_synced_between_gate_and_full() -> None:
	ordered_theorem_tokens = [
		"sr_inevitability_necessity_under_minimized_assumptions_v0",
		"sr_inevitability_counterfactual_breaks_without_required_assumption_v0",
		"sr_inevitability_structural_classification_of_constructive_route_v0",
		"sr_inevitability_discharge_ready_bundle_v0",
		"sr_inevitability_route_bundle_without_shortcuts_v0",
		"sr_inevitability_physics_substance_dependency_bundle_v0",
		"sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0",
		"sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
	]
	ordered_anchor_tokens = [
		"SRInevitabilityMinimizedAssumptions_v0",
		"SRInevitabilityCanonicalCovarianceRoute_v0",
		"SRInevitabilityIntervalInvariantRoute_v0",
		"SRInevitabilityNoShortcutRoute_v0",
		"SRInevitabilityClosureSurface_v0",
	]
	_assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_theorem_tokens, "SR inevitability gate target theorem-order")
	_assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_theorem_tokens, "SR full-derivation target theorem-order")
	_assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_anchor_tokens, "SR inevitability gate target anchor-order")
	_assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_anchor_tokens, "SR full-derivation target anchor-order")


def test_sr_inevitability_linkage_section_precedes_cycle57_in_gate_and_full_targets() -> None:
	gate_text = _read(TARGET_GATE_PATH)
	full_text = _read(TARGET_FULL_PATH)

	gate_linkage_idx = gate_text.find("Inevitability obligation linkage")
	gate_cycle57_idx = gate_text.find("Cycle-057 phase-VI inevitability necessity theorem-surface lock")

	full_linkage_idx = full_text.find("Inevitability obligation linkage")
	full_cycle57_idx = full_text.find("Cycle-057 phase-VI inevitability necessity theorem-surface lock")

	assert gate_linkage_idx != -1, "SR gate target is missing inevitability obligation linkage section."
	assert gate_cycle57_idx != -1, "SR gate target is missing Cycle-057 inevitability section."
	assert gate_linkage_idx < gate_cycle57_idx, (
		"SR gate target inevitability obligation linkage must appear before Cycle-057 section."
	)

	assert full_linkage_idx != -1, "SR full target is missing inevitability obligation linkage section."
	assert full_cycle57_idx != -1, "SR full target is missing Cycle-057 inevitability section."
	assert full_linkage_idx < full_cycle57_idx, (
		"SR full target inevitability obligation linkage must appear before Cycle-057 section."
	)
