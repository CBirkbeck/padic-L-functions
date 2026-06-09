# p-adic L-functions in Lean

A Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalisation of the lecture notes

> J. Rodrigues Jacinto and C. Williams,
> **An introduction to p-adic L-functions**,
> [arXiv:2309.15692](https://arxiv.org/abs/2309.15692).

The notes construct the **Kubota–Leopoldt p-adic L-function** $\zeta_p$, prove
that it interpolates the special values $\zeta(1-n) = -B_n/n$ of the Riemann zeta
function, and develop the cyclotomic Iwasawa theory needed to state and (for
Vandiver primes) prove the **Iwasawa Main Conjecture**, before sketching the
$\mathrm{GL}(2)$ analogue for modular forms.

## Status

**Roadmap stage.** The [blueprint](#blueprint) records the intended statements and
proof sketches for the whole paper (§2–§15). Lean skeletons are being introduced
incrementally; the blueprint dependency graph colours each node in as the
declaration it references is stated (blue) and then fully proved (green).

## Layout

| Path | Contents |
|------|----------|
| `PadicLFunctions/` | the formalisation library (Lean) |
| `PadicLFunctionsBlueprint/` | the Verso blueprint: `Blueprint.lean` (top-level), `Chapters/`, `Refs.lean` |
| `.mathlib-quality/references/` | the source notes (TeX) used while authoring |
| `scripts/ci-pages.sh` | build the blueprint HTML site locally |
| `home_page/` | GitHub Pages landing page |

## Building

This is a standard Lake project pinned to a recent Mathlib (toolchain in
`lean-toolchain`).

```bash
# fetch the prebuilt Mathlib cache, then build the formalisation library
lake exe cache get
lake build PadicLFunctions
```

## Blueprint

The mathematical blueprint is a [Verso](https://github.com/leanprover/verso)
document (the tooling behind `verso-sphere-packing`, `verso-flt`, …). To render
the HTML site locally:

```bash
./scripts/ci-pages.sh   # output in _out/site/html-multi/
```

Once published, it will live at
<https://CBirkbeck.github.io/padic-L-functions/>.

## Credits

Formalisation by Chris Birkbeck. The mathematics is due to Joaquín Rodrigues
Jacinto and Chris Williams; see the notes above. Released under the Apache 2.0
license (see `LICENSE`).
