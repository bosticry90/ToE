# Repo Integrity Run 2026-02-14

UTC run stamp: `2026-02-14T20:00:17Z`

## Baseline artifacts

- `formal/tooling_snapshots/repo_snapshot_20260214_integrity_baseline.jsonl`
  - size: `39925645` bytes
  - written: `2026-02-14 19:52:24Z`
- `formal/tooling_snapshots/repo_snapshot_20260214_integrity_post.jsonl`
  - size: `39925645` bytes
  - written: `2026-02-14 19:55:16Z`
- `formal/output/repo_integrity_diff_20260214.txt`
  - size: `34` bytes
  - written: `2026-02-14 19:55:28Z`
  - contents: `COUNTS new=0 modified=0 missing=0`

## Tracked-only suite confirmation

- command: ``$files = git ls-files "formal/python/tests/*.py"; .\py.ps1 -m pytest @files``
- result: `659 passed, 1 skipped`
- duration: `260.85s`

## Replay commands (post power-loss check)

1. Build current snapshot:
   - `.\py.ps1 -m formal.python.tools.repo_hygiene_snapshot snapshot --out formal/tooling_snapshots/repo_snapshot_<YYYYMMDD>_<HHMMSS>_current.jsonl`
2. Diff against baseline:
   - `.\py.ps1 -m formal.python.tools.repo_hygiene_snapshot diff --baseline formal/tooling_snapshots/repo_snapshot_20260214_integrity_baseline.jsonl --current formal/tooling_snapshots/repo_snapshot_<YYYYMMDD>_<HHMMSS>_current.jsonl --profile sanity --ignore-quarantine --out formal/output/repo_integrity_diff_<YYYYMMDD>.txt`
3. Reconfirm tracked-only tests:
   - ``$files = git ls-files "formal/python/tests/*.py"; .\py.ps1 -m pytest @files``
