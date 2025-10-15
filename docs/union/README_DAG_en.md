# DAG Layout Rules (English Only)

- Each layer is `LXX/` (two digits), forming a DAG of theory dependencies.
- Lower layers (higher numbers) may reference upper layers (lower numbers).
- Same‑layer references are forbidden.
- No gaps in the proof chain: each lemma/theorem states its upstream dependencies and downstream links.
- Canonical expressions and full (non‑abbreviated) formulas only; conflicts are recorded and resolved later.
