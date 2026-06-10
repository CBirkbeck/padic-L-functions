# padic-L-functions — project instructions

Lean 4 / Mathlib formalisation of Rodrigues Jacinto–Williams, *An introduction to
p-adic L-functions* (arXiv:2309.15692). Source TeX:
`.mathlib-quality/references/2309.15692-padic-L-functions.tex` (cite TeX line numbers).

## Standing rules (binding for every work session)

1. **Workflow**: plan with `/develop` (per paper section), execute with `/beastmode`.
   Planning artifacts live in `.mathlib-quality/{plan,decomposition,tickets}.md` and are
   the source of truth for what's proven and what's next.

2. **Blueprint stays in sync as we go.** The Verso blueprint
   (`PadicLFunctionsBlueprint/Chapters/*.lean`) is updated *in the same work cycle* as
   the Lean code, not in a batch afterwards:
   - When a declaration reaches sorry-free, add/update the matching chapter node's
     `(lean := "...")` reference in the same session (the node then renders green).
   - If a /develop pass restates or renames a planned declaration, fix the chapter
     node's statement/prose to stay faithful to both the source and the Lean.
   - Nodes for deferred material (see plan.md "Deferred") stay unwired — never wire a
     node to a *project* declaration that only partially realises it.
   - **Mathlib linking (user directive 2026-06-10)**: where a node's content is
     already formalised in mathlib, wire the node to the mathlib declaration — and
     this *may* be something more general than the notes' statement (e.g. valuations
     ↦ `ValuativeRel`/`IsUltrametricDist`). When the mathlib form differs from the
     notes' (one-sided limit vs residue, series vs continuation, B₁-convention), add
     a one-sentence prose note in the node recording the difference. The blueprint
     is filled in chapter by chapter as the formalisation reaches each section, and
     each section's pass includes a mathlib-linking sweep of its chapter.
   - All chapters share the single KaTeX macro prelude in
     `PadicLFunctionsBlueprint/TexPrelude.lean` — never add a per-chapter
     `tex_prelude` (divergent per-module preludes overwrite each other in the
     rendered site's shared macro table; that was the raw-`\CC`/`\roi` bug).
   - After wiring, `lake build PadicLFunctionsBlueprint` must pass (it verifies the
     refs resolve) and re-render with `./scripts/ci-pages.sh` when convenient.

3. **Cleanup immediately after proving.** When a proof ticket reaches sorry-free +
   axiom-clean, run `/cleanup` on the new declaration(s) (single-declaration mode)
   before marking the ticket done — don't batch cleanups to the end of a file. If the
   session lacks the lean-lsp MCP tools, run the degraded pass (build with the mathlib
   linter set green + manual golf of obvious slack) and record "degraded mode" in the
   ticket so a tooled session can revisit.

4. **Verification bar per ticket**: `lake build` green, zero `sorry` in the new
   declarations, `#print axioms` shows only `propext`, `Classical.choice`,
   `Quot.sound`. Record the check in the ticket's Progress notes.

5. **Source-faithfulness**: every planned leaf carries a verbatim TeX quote
   (decomposition.md); proofs may take Lean-friendlier routes only when recorded as a
   replan note in the ticket (see T018/T026 for the pattern). p = 2 is excluded
   wherever the source assumes p odd — never silently drop that hypothesis.
   User re-affirmed 2026-06-10: "we follow the paper as closely as possible" — when a
   Lean-friendlier route is tempting, prefer the paper's route; replan notes are the
   exception, not the rule, and statements/definitions must match the paper's even
   when mathlib offers a different-but-equivalent formulation.

6. **Coefficients**: ℤ_p for now; the O_L generalisation is a dedicated pass when §5
   needs it (plan.md "Generality Decisions"). Don't widen ad hoc.

7. **Commits**: checkpoint commit after each completed ticket (or tight group);
   pushes to `origin main` are pre-approved for this repo.

## Layout

- `PadicLFunctions/Measure/` — §3 measure theory (COMPLETE, sorry-free 2026-06-10)
- `PadicLFunctionsBlueprint/Chapters/` — Verso blueprint, one chapter per paper section
- `.mathlib-quality/` — plan, decomposition (verbatim quotes + attack logs), tickets
- Build: `lake build PadicLFunctions` (code), `lake build PadicLFunctionsBlueprint`
  (blueprint), `./scripts/ci-pages.sh` (HTML site to `_out/site/html-multi/`)
