---
usemathjax: true
---

# An introduction to p-adic L-functions, in Lean

This project is a Lean 4 / Mathlib formalisation of the lecture notes

> J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
> [arXiv:2309.15692](https://arxiv.org/abs/2309.15692).

The notes construct the **Kubota–Leopoldt $p$-adic $L$-function** $\zeta_p$,
prove that it interpolates the special values

\\[
  \zeta(1-n) = -\frac{B_n}{n}
\\]

of the Riemann zeta function, and develop the cyclotomic Iwasawa theory needed to
state and prove the **Iwasawa Main Conjecture** (following the notes, for Vandiver
primes), before sketching the analogous $\mathrm{GL}(2)$ picture for modular forms.

## Useful links

* [Blueprint (HTML)]({{ site.url }}/blueprint/)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Source on GitHub](https://github.com/CBirkbeck/padic-L-functions)

## References

* J. Rodrigues Jacinto, C. Williams, *An introduction to p-adic L-functions*,
  arXiv:2309.15692.
* L. C. Washington, *Introduction to Cyclotomic Fields*, GTM 83, Springer.
* R. F. Coleman, *Division values in local fields*, Invent. Math. 53 (1979).
