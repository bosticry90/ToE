# OV-BR-SND-03 Bragg↔Sound pairing mapping (governance-only)

This directory holds the **explicit Bragg↔Sound pairing mapping** consumed by the OV-BR-SND-03 cross-lane audit.

## Key safety rule

Adding any tuple here is an **explicit pairing claim**. Do not add tuples unless you can justify them with pinned evidence.

Until such evidence exists, keep the mapping strictly empty:

- `mapping_tuples.json`: `"mapping_tuples": []`

## File

- `mapping_tuples.json`
  - `schema`: `OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4`
  - `mapping_tuples`: list of pairing tuples (may be empty)

## Tuple shape (template)

A tuple is a JSON object with these keys:

- `tuple_id` (string): stable identifier (must be unique within the file)
- `bragg_key` (string): one of
  - `br04a_conditionA`
  - `br04b_conditionB`
- `sound_key` (string): one of
  - `snd02_single`
  - `snd02b_seriesB`
- `pair_type` (string): one of
  - `same_source`
  - `cross_source_established`
  - `cross_source_hypothesis`
- `rationale` (string): short explanation of why this pairing is valid
- `source_locators` (object): pointers to pinned evidence (paths should generally be under `formal/`)

## Upgrade gating (intended)

- Only **justified** pairings may allow OV-BR-SND-03 to compute comparisons and upgrade comparability.
- `pair_type: cross_source_hypothesis` must **never** be treated as justification for upgrading to `established`.

(Exact enforcement lives in code; this README is a governance aid and intentionally contains no tuples.)
