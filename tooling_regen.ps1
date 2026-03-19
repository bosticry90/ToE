$ErrorActionPreference = 'Stop'

Write-Host "Running tooling regeneration checks via ./py.ps1" -ForegroundColor Cyan

try {
	# Bragg lane regeneration.
	./py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only --report

	# Sound lane regeneration.
	./py.ps1 -m formal.python.tools.regen_canonical_locks --snd-only --report

	Write-Host "OK" -ForegroundColor Green
	exit 0
}
catch {
	Write-Host "FAILED" -ForegroundColor Red
	Write-Host $_.Exception.Message -ForegroundColor Red
	exit 1
}
