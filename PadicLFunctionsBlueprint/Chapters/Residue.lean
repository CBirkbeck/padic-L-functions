import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\Zp{\mathbb{Z}_p}\def\Qp{\mathbb{Q}_p}\def\Cp{\mathbb{C}_p}\def\Fp{\mathbb{F}_p}\def\Zpx{\mathbb{Z}_p^{\times}}\def\Qpx{\mathbb{Q}_p^{\times}}\def\Qbar{\overline{\mathbb{Q}}}\def\Qpbar{\overline{\mathbb{Q}_p}}\def\cO{\mathcal{O}}\def\cC{\mathcal{C}}\def\cH{\mathcal{H}}\def\cG{\mathcal{G}}\def\cN{\mathcal{N}}\def\cM{\mathcal{M}}\def\cD{\mathcal{D}}\def\cA{\mathcal{A}}\def\sX{\mathscr{X}}\def\sY{\mathscr{Y}}\def\sM{\mathscr{M}}\def\sL{\mathscr{L}}\def\sU{\mathscr{U}}\def\sW{\mathscr{W}}\def\sE{\mathscr{E}}\def\Gal{\mathrm{Gal}}\def\Frob{\mathrm{Frob}}\def\Lam{\Lambda}\def\Teich{\omega}\def\ord{\mathrm{ord}}\def\val{\mathrm{val}}\def\res{\operatorname{res}}\def\Res{\operatorname{Res}}\def\Tr{\mathrm{Tr}}\def\Nm{\mathrm{N}}\def\Mahler{\mathfrak{M}}\def\Mellin{\mathrm{Mel}}\def\Exp{\mathrm{Exp}}\def\Col{\mathrm{Col}}\def\Log{\mathrm{Log}}\def\charid{\mathrm{char}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}\def\set#1{\left\{#1\right\}}\def\floor#1{\left\lfloor#1\right\rfloor}\def\Rp{\mathscr{R}^{+}}\def\zp{\zeta_p}\def\zpi{\zeta_{p,i}}\def\Fat{\widetilde{F}_a}\def\logp{\log_p}\def\dpartial{\partial}"#

#doc (Manual) "The residue at s = 1" =>

The Riemann zeta function $`\zeta(s)` has a simple pole at $`s=1` with residue
$`1`. On the $`p`-adic side we constructed $`\zp` not as a measure but as a
*pseudo-measure*, precisely so as to accommodate a
potential pole at the trivial character. In this chapter we show that this pole
is real and simple, and we compute its residue — the $`p`-adic analogue of the
analytic class number formula. Throughout, $`p` is a fixed odd prime, $`a` is a
fixed topological generator of $`\Zpx`, and $`\logp` denotes the Iwasawa
$`p`-adic logarithm.

As in the chapter on the value at $`s=1`, it is convenient to phrase everything
through the analytic *branches* $`\zpi` of the $`p`-adic zeta function: for
$`i \in \set{1, 2, \ldots, p-1}` one sets
$$`\zpi(s) = \int_{\Zpx} \Teich(x)^{i}\,\ang{x}^{1-s} \cdot \zp,`
where $`\Teich` is the Teichmüller character and
$`\ang{x} = \Teich(x)^{-1}x` is the projection of $`x \in \Zpx` to its
$`1`-units. The behaviour of $`\zp` at the trivial character is encoded by the
behaviour of $`\zeta_{p,p-1}` at $`s=1`.

# The main theorem

:::theorem "residue-zeta-p"
Let $`i \in \set{1, 2, \ldots, p-1}`.

* (i) If $`i \neq p-1`, then $`\zpi` is analytic at $`s=1`.
* (ii) The branch $`\zeta_{p,p-1}` has a simple pole at $`s=1`, with residue
  $$`\lim_{s\to 1} (s-1)\,\zeta_{p,p-1}(s) = 1 - p^{-1}.`

This rests on {uses "kubota-leopoldt"}[], {uses "res-g-pminus1"}[] and
{uses "res-numerator"}[].
:::

:::proof "residue-zeta-p"
Part (i) is immediate from {uses "res-g-pminus1"}[](i): unwinding the definition
of $`\zp` as a pseudo-measure expresses $`\zpi(s)` as a ratio whose denominator
$`g_{a,i}(s)` does not vanish at $`s=1` when $`i \neq p-1`, so the expression is
analytic there. For part (ii), the same unwinding gives, after passing to the
limit using {uses "res-limit-formula"}[],
$$`\lim_{s\to 1}(s-1)\,\zeta_{p,p-1}(s) = -\frac{\int_{\Zpx} x^{-1}\cdot \mu_a}{\logp(a)}.`
By {uses "res-integral-as-eval"}[] the numerator $`\int_{\Zpx} x^{-1}\cdot\mu_a`
equals $`\big((1-\varphi\circ\psi)\Fat\big)(0)`, which by {uses "res-numerator"}[]
is $`-(1-p^{-1})\logp(a)`; the two factors of $`\logp(a)` then cancel to leave
$`1 - p^{-1}`.
:::

# Unwinding the pseudo-measure

Recall from the construction of $`\zp` that, for any topological generator $`a`
of $`\Zpx`,
$$`\zp = \frac{x^{-1}\,\Res_{\Zpx}(\mu_a)}{[a]-[1]},`
where the $`\mu_a` are the Kubota–Leopoldt measures. Using
the rule $`\int_G \chi\cdot\lambda = (\chi(g)-1)^{-1}\int_G \chi\cdot([g]-[1])\lambda`
for integrating a pseudo-measure $`\lambda` against a non-trivial character, and
the identity $`\ang{x} = \Teich^{-1}(x)\,x`, the branch $`\zpi` becomes a ratio.

:::definition "res-denominator-g"
For $`i \in \set{1,\ldots,p-1}` define the *denominator*
$$`g_{a,i}(s) := \Teich(a)^{i}\,\ang{a}^{1-s} - 1.`
Substituting $`\zp = x^{-1}\Res_{\Zpx}(\mu_a)/([a]-[1])` into the definition of
$`\zpi` and integrating the pseudo-measure yields the closed form
$$`\zpi(s) = \frac{\int_{\Zpx} \Teich(x)^{s+i-1}\,x^{-s}\cdot \mu_a}{g_{a,i}(s)}.`
This rests on {uses "kubota-leopoldt"}[], {uses "measure-mu-a"}[] and
{uses "pseudo-measure"}[].
:::

:::lemma_ "res-g-pminus1"
With $`g_{a,i}` as above:

* (i) If $`i \neq p-1`, then $`g_{a,i}(1) \neq 0`. Consequently
  {uses "residue-zeta-p"}[Theorem (i)] holds.
* (ii) $`g_{a,p-1}(1) = 0`, and
  $$`\lim_{s\to 1} (s-1)^{-1}\,g_{a,p-1}(s) = -\logp(a).`

This depends on {uses "res-denominator-g"}[] and
{uses "teichmuller-character"}[].
:::

:::proof "res-g-pminus1"
Since $`a` is a topological generator of $`\Zpx`, its image $`\Teich(a)` is a
*primitive* $`(p-1)`-th root of unity. At $`s=1` the factor $`\ang{a}^{1-s}=1`,
so $`g_{a,i}(1) = \Teich(a)^{i}-1`, which vanishes exactly when $`(p-1)\mid i`,
i.e. when $`i=p-1`. This proves (i): the closed form of {uses "res-denominator-g"}[]
then has a non-vanishing denominator at $`s=1` and is therefore analytic there.

For (ii), with $`i=p-1` we have $`\Teich(a)^{p-1}=1`, so
$`g_{a,p-1}(s) = \ang{a}^{1-s}-1`. Expanding the binomial series in
$`(\ang{a}-1)` gives
$$`g_{a,p-1}(s) = \sum_{n\ge 1}\binom{1-s}{n}(\ang{a}-1)^n = (1-s)\sum_{n\ge 1}\frac{1}{n}\binom{-s}{n-1}(\ang{a}-1)^n,`
using $`\binom{1-s}{n} = \tfrac{1-s}{n}\binom{-s}{n-1}`. As $`s\to 1` the
remaining sum tends to its value at $`s=1`, namely
$$`\sum_{n\ge 1}\frac{(-1)^{n-1}}{n}(\ang{a}-1)^n = \logp(\ang{a}) = \logp(a),`
where $`\binom{-1}{n-1}=(-1)^{n-1}` and $`\logp(\ang{a})=\logp(a)` because
$`\logp\Teich(a)=0`. Hence $`\lim_{s\to1}(s-1)^{-1}g_{a,p-1}(s) = -\logp(a)`.
:::

:::corollary "res-limit-formula"
Combining {uses "res-g-pminus1"}[](ii) with the closed form
{uses "res-denominator-g"}[] of $`\zeta_{p,p-1}`,
$$`\lim_{s\to 1} (s-1)\,\zeta_{p,p-1}(s) = -\frac{\int_{\Zpx} x^{-1}\cdot \mu_a}{\logp(a)}.`
:::

:::proof "res-limit-formula"
In the closed form $`\zeta_{p,p-1}(s) = \big(\int_{\Zpx}\Teich(x)^{s+p-2}x^{-s}\mu_a\big)/g_{a,p-1}(s)`
of {uses "res-denominator-g"}[], the numerator is analytic in $`s` and at $`s=1`
equals $`\int_{\Zpx} x^{-1}\cdot\mu_a` (since $`\Teich(x)^{p-1}=1` makes the
integrand $`\Teich(x)^{p-1}x^{-1}=x^{-1}`). The denominator $`g_{a,p-1}(s)`
vanishes to first order at $`s=1`. Multiplying by $`(s-1)` and using
{uses "res-g-pminus1"}[](ii), which gives $`(s-1)/g_{a,p-1}(s) \to 1/(-\logp(a))`,
the analytic numerator passes through the limit and yields the stated formula.
:::

# Computing the numerator

It remains to evaluate $`\int_{\Zpx} x^{-1}\cdot\mu_a`. As in the chapter on the
value at $`s=1`, the difficulty is that
multiplication by $`x^{-1}` is not defined on measures on $`\Zp`; on
Mahler transforms this is the indeterminacy in
inverting the operator $`\dpartial = (1+T)\tfrac{d}{dT}`. Recall that the Mahler
transform of $`\mu_a` is $`F_a(T) = \tfrac{1}{T} - \tfrac{a}{(1+T)^a-1}`. We seek
a primitive $`\Fat` with $`\dpartial\Fat = F_a`, lying in the ring $`\Rp` of
power series $`\sum a_n T^n` with $`\abs{a_n}r^n \to 0` for every $`0\le r<1`.

:::definition "res-primitive-Fa"
Define the *primitive of $`F_a`* by
$$`\Fat(T) := \log\!\left(\frac{T}{1+T}\cdot\frac{(1+T)^a}{(1+T)^a-1}\right) = \log\!\left(\frac{T}{(1+T)^a-1}\cdot (1+T)^{a-1}\right).`
:::

:::lemma_ "res-primitive-derivative"
Formally, $`\dpartial \Fat(T) = F_a(T)`. This depends on
{uses "res-primitive-Fa"}[] and {uses "mahler-transform"}[].
:::

:::proof "res-primitive-derivative"
The operator $`\dpartial = (1+T)\tfrac{d}{dT}` satisfies the chain rule, so for
any unit power series $`u` one has $`\dpartial\log u = (1+T)u'/u`. Applied to
$`u = \tfrac{(1+T)^a-1}{(1+T)^a}`, whose logarithmic derivative computes to
$`(1+T)\big[\tfrac{a(1+T)^{a-1}}{(1+T)^a-1} - \tfrac{a(1+T)^{a-1}}{(1+T)^a}\big]`,
this collapses (after clearing $`(1+T)^a`) to
$`\dpartial\log\big(\tfrac{(1+T)^a-1}{(1+T)^a}\big) = \tfrac{a}{(1+T)^a-1}`.
Specialising to $`a=1` gives $`\dpartial\log\big(\tfrac{T}{1+T}\big) = \tfrac1T`.
Since $`\Fat = \log\big(\tfrac{T}{1+T}\big) - \log\big(\tfrac{(1+T)^a-1}{(1+T)^a}\big)`,
linearity of $`\dpartial` yields
$`\dpartial\Fat = \tfrac1T - \tfrac{a}{(1+T)^a-1} = F_a(T)`, the Mahler transform
of $`\mu_a`.
:::

:::lemma_ "res-Fa-tilde-bounded"
We have $`\Fat(T) \in \Rp`, so that $`\Fat` corresponds under the Mahler
correspondence to a locally analytic distribution. This depends on
{uses "res-primitive-Fa"}[] and {uses "mahler-transform"}[].
:::

:::proof "res-Fa-tilde-bounded"
Write $`(1+T)^a-1 = aT\,(1+Tg(T))` with $`g(T) = \sum_{n\ge 2} a^{-1}\binom{a}{n}T^{n-2}`,
so that, as in the construction of $`\mu_a`,
$`\tfrac{1}{(1+T)^a-1} = \tfrac{1}{aT}(1+Th(T))` with $`h(T)\in\Zp[[T]]`. Hence
$`\tfrac{T}{(1+T)^a-1} = a^{-1}(1+Th(T))`, and
$$`\log\!\left(\frac{T}{(1+T)^a-1}\right) = -\logp(a) + \sum_{n\ge 1}\frac{(-1)^{n+1}}{n}T^n h(T)^n.`
The coefficients here grow only logarithmically in $`n` (the $`1/n` is offset by
$`\val(n)`), so this series lies in $`\Rp`. Likewise
$`(1+T)^{a-1} = 1 + T\sum_{n\ge1}\binom{a-1}{n}T^{n-1}` has a well-defined
logarithm in $`\Rp`. Adding the two elements of $`\Rp` yields $`\Fat \in \Rp`.
:::

With $`\Fat \in \Rp` in hand we may attach to it a locally analytic distribution
$`\widetilde\mu_a` (the one whose Mahler transform is $`\Fat`), and the relation
$`\dpartial\Fat = F_a` says precisely that $`x\,\widetilde\mu_a = \mu_a`. This is
the device that makes sense of the otherwise ill-defined product $`x^{-1}\mu_a`.

:::lemma_ "res-integral-as-eval"
The numerator of the residue formula is the value at $`0` of the restriction of
$`\Fat` to $`\Zpx`:
$$`\int_{\Zpx} x^{-1}\cdot\mu_a = \big((1-\varphi\circ\psi)\Fat\big)(0),`
where $`\varphi\circ\psi` acts on power series by
$`\varphi\circ\psi(F)(T) = \tfrac1p\sum_{\xi\in\mu_p} F((1+T)\xi - 1)`. This
depends on {uses "res-primitive-derivative"}[], {uses "res-Fa-tilde-bounded"}[],
{uses "locally-analytic-distribution"}[] and {uses "p-adic-value-s1"}[].
:::

:::proof "res-integral-as-eval"
On $`\Zpx` the function $`x` is invertible, so $`x\,\widetilde\mu_a = \mu_a`
gives $`\Res_{\Zpx}(\widetilde\mu_a) = x^{-1}\Res_{\Zpx}(\mu_a)` and hence
$`\int_{\Zpx} x^{-1}\cdot\mu_a = \int_{\Zpx}\widetilde\mu_a`. The right-hand side
is the value at the trivial character of the restricted distribution, which on
Mahler transforms is read off as the constant term: writing $`\Res_{\Zpx} =
1-\varphi\circ\psi` (the complement of restriction to $`p\Zp`, whose Mahler
transform is $`\varphi\circ\psi\Fat`), one gets
$`\int_{\Zpx}\widetilde\mu_a = \big((1-\varphi\circ\psi)\Fat\big)(0)`. This is the
exact analogue, with $`\Fat` in place of $`\widetilde F_\theta`, of the
computation that produced the value at $`s=1`. This reduces the residue
computation to a single evaluation.
:::

:::lemma_ "res-numerator"
We have
$$`\big((1-\varphi\circ\psi)\Fat\big)(0) = -(1-p^{-1})\,\logp(a).`
This depends on {uses "res-primitive-Fa"}[] and {uses "res-Fa-tilde-bounded"}[].
:::

:::proof "res-numerator"
*Value of $`\Fat(0)`.* From the second expression in {uses "res-primitive-Fa"}[],
$`\Fat(0) = \log\big(\tfrac{T}{(1+T)^a-1}\big)\big|_{T=0} + \log((1+T)^{a-1})\big|_{T=0}`;
the first summand equals $`-\logp(a)` by the expansion in
{uses "res-Fa-tilde-bounded"}[] and the second is $`0`, so $`\Fat(0) = -\logp(a)`.

*Value of $`(\varphi\circ\psi)\Fat(0)`.* Summing the logarithm over $`\xi\in\mu_p`
turns the sum into the logarithm of a product, and
$`\prod_{\xi\in\mu_p}(X\xi-1) = X^p-1` collapses each factor. Using that $`a` is a
topological generator (so $`\set{\xi^a:\xi\in\mu_p}=\mu_p`) and
$`\prod_{\xi\in\mu_p}\xi^{a-1}=1`,
$$`(\varphi\circ\psi)\Fat(T) = \frac1p\log\!\left(\frac{(1+T)^p-1}{(1+T)^{ap}-1}\cdot (1+T)^{(a-1)p}\right).`
Writing $`(1+T)^p-1 = pT(1+Tj(T))` and $`\tfrac{1}{(1+T)^{ap}-1} = \tfrac{1}{apT}(1+Tk(T))`
as before, the factors of $`pT` cancel and the right-hand side at $`T=0`
collapses to $`-p^{-1}\logp(a)`.

*Conclusion.* Subtracting the two evaluations,
$$`\big((1-\varphi\circ\psi)\Fat\big)(0) = \Fat(0) - (\varphi\circ\psi)\Fat(0) = -\logp(a) - p^{-1}\logp(a) = -(1-p^{-1})\,\logp(a),`
as claimed.
:::

Combining the limit formula with the value of the numerator, the two
occurrences of $`\logp(a)` cancel and we obtain
$$`\lim_{s\to 1}(s-1)\,\zeta_{p,p-1}(s) = -\frac{-(1-p^{-1})\logp(a)}{\logp(a)} = 1 - p^{-1},`
completing the proof of the residue theorem. The residue
$`1-p^{-1}` is the precise $`p`-adic shadow of the residue $`1` of the complex
$`\zeta` at $`s=1`: it is $`\zeta(s)` with its Euler factor at $`p` removed,
evaluated at the pole.
