\# Import Contract (ToE Repo)



\## Purpose

Keep the repository runnable from repo root, keep tests deterministic, and prevent “accidental” coupling between current code and archived/legacy code.



\## The rule of three

1\) \*\*Current code imports current code.\*\*

2\) \*\*Archive code is never imported by default test runs.\*\*

3\) \*\*Tests import packages, not files.\*\*



\## Canonical import style

\### A) Allowed (current code)

\- Absolute imports from repo-root packages:

&nbsp; - `import toe...`

&nbsp; - `import numerics...`

&nbsp; - `import field\_theory...`

&nbsp; - `import equations...`

&nbsp; - `import fundamental\_theory...`

&nbsp; - `import common...`

&nbsp; - `import mei...`

&nbsp; - `import examples...` (examples should not be imported by tests unless explicitly intended)



\### B) Allowed (within a package)

\- Intra-package relative imports:

&nbsp; - `from .submodule import ...`

&nbsp; - `from . import helpers`



\### C) Disallowed

\- Importing archive code from current code:

&nbsp; - `import archive...` or `from archive...`

\- Path-based / file-based imports:

&nbsp; - `sys.path.append(...)` inside library code (tests may have a controlled path shim if required)

&nbsp; - `import <filename\_without\_package>` from random working directories

\- Using multiple names for the same package root (avoid aliasing the same codebase under different import paths)



\## Test collection contract

\- Default test run (`pytest`) must only run “current” tests.

\- Archive/legacy tests must be run explicitly and must not block the default run.



\## Public API surface

Each top-level package provides a `public\_api.py` that documents what is stable to import.

Anything not listed there is internal and may change without notice.



\## Legacy archive policy

\- `archive/` is a cold-storage namespace.

\- It may include code and tests that no longer match the current public API.

\- Legacy tests are allowed to fail without blocking the current suite unless explicitly promoted back into current scope.



