# Repository Guidelines

## Project Structure & Module Organization
- Primary sources live in `docs/`; the mdBook chapters sit in numbered `chapterXX_*` files, while thematic collections (e.g., `docs/the-matrix`, `docs/traditional-math`) hold deeper theory stacks.
- Generated HTML lands in `book/`; treat it as build output—inspect it locally but avoid committing edits there.
- Python utilities (`merge_chapters.py`, `merge_q_series.py`) and helpers under `tools/` automate large compendiums; keep new automation scripts alongside them.
- `tests/` is currently a placeholder for future validation suites; prefer adding notebook-style checks inside `docs/` until formal tests arrive.

## Build, Test, and Development Commands
- `mdbook build` compiles Markdown from `docs/` into the `book/` directory; run it before every PR to catch broken links or math formatting issues.
- `mdbook serve --open` watches the sources and refreshes the rendered book—ideal for iterative chapter editing.
- `python merge_chapters.py` assembles the Recursive Hilbert compendium at `docs/COMPLETE_RECURSIVE_HILBERT_THEORY.md`; rerun after touching `docs/traditional-math/hilbert-complete`.
- `python merge_q_series.py` rebuilds the ZkT anthology; execute it whenever the Q-series folders change to keep downstream docs synchronized.

## Coding Style & Naming Conventions
- Markdown: keep top-level headings unique, favor short declarative titles, and mirror existing numbering (`chapter04_hilbert.md`, `Q02.5-*`).
- Python: follow 4-space indentation, type hints where feasible, and descriptive docstrings similar to the existing merge utilities.
- Assets: store reusable diagrams in `docs/math/` or the relevant thematic subfolder; reference them with relative paths.

## Testing Guidelines
- Treat a clean `mdbook build` as the minimum regression check; review warnings for misplaced front matter or Mermaid diagrams.
- For generator scripts, run them directly and skim the regenerated Markdown diffs to confirm heading levels and section order.
- When experimenting with computational notebooks or prototypes, stage them under `ref/` and document manual validation steps in commit messages.

## Commit & Pull Request Guidelines
- Follow the short, scope-first commit style used in history (`5.4 5.5`, `update summary`); call out the chapter or tool touched in the subject.
- Each PR should summarize the affected sections, list the commands you ran (e.g., `mdbook build`), and link any relevant issue or planning note.
- Attach rendered screenshots only when visual layout changes; otherwise reference the generated page path (e.g., `book/chapter04_hilbert.html`).

## Agent Workflow Notes
- `CLAUDE.md` defines the coordination protocol: verify downstream agents complete their workflow before merging.
- When delegating, write explicit entry points (file path, command) so fellow agents can pick up work without re-scanning the tree.
