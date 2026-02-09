$ErrorActionPreference = 'Stop'

Write-Host "Running tooling smoke checks via ./py.ps1" -ForegroundColor Cyan

try {
	./py.ps1 -c "import formal.python.tools.regen_canonical_locks as m; print('import ok: regen_canonical_locks')"
	./py.ps1 -c "import formal.python.tools.lint_mapping_tuples as m; print('import ok: lint_mapping_tuples')"
	./py.ps1 -c "import formal.python.tools.ovsw01_shallow_water_lowk_slope_record as m; print('import ok: ovsw01_shallow_water_lowk_slope_record')"

	# Deterministic governance lint (fails fast on drift).
	./py.ps1 -m formal.python.tools.lint_mapping_tuples --fail-fast

	# Bragg lane regen guardrail.
	./py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only --report

	# Sound lane regen guardrail.
	./py.ps1 -m formal.python.tools.regen_canonical_locks --snd-only --report

	# Cross-lane audit (must be safe even without mapping).
	./py.ps1 -m formal.python.tools.ovbr_snd03_cross_lane_lowk_consistency_audit_record --no-write --report

	# Axis C stub observable (must be safe even without digitized data).
	./py.ps1 -m formal.python.tools.ovsw01_shallow_water_lowk_slope_record --no-write --report

	Write-Host "OK" -ForegroundColor Green
	exit 0
}
catch {
	Write-Host "FAILED" -ForegroundColor Red
	Write-Host $_.Exception.Message -ForegroundColor Red
	exit 1
}
