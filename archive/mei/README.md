\# MEI literate build system



\## Layout

\- `mei/template.tex` — canonical LaTeX shell with insertion token.

\- `mei/mei\_order.yaml` — ordered list of blocks relative to `mei/blocks/`.

\- `mei/blocks/` — content blocks (`.tex` or `.md`).

\- `mei/checks/` — preflight validation scripts.

\- `mei/weave\_mei.py` — deterministic weaver.



\## Build

1\. Run checks:

&nbsp;  - `python mei/checks/check\_braces.py mei/blocks`

&nbsp;  - `python mei/checks/check\_align.py mei/blocks`

&nbsp;  - `python mei/checks/check\_macros.py mei/blocks mei/template.tex`

&nbsp;  - `python mei/checks/check\_order.py mei/mei\_order.yaml mei/blocks`



2\. Weave:

&nbsp;  - `python mei/weave\_mei.py mei/mei\_order.yaml mei/template.tex > MEI\_vX.tex`



3\. Compile:

&nbsp;  - `pdflatex MEI\_vX.tex`



Checks must pass before weaving. Weaving must succeed before pdflatex.



