import PadicLFunctions.Basic
import PadicLFunctions.Measure.Basic
import PadicLFunctions.Measure.MahlerTransform
import PadicLFunctions.Measure.Convolution
import PadicLFunctions.Measure.Toolbox
import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.Measure.Fubini
import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.KubotaLeopoldt.ZetaValues
import PadicLFunctions.KubotaLeopoldt.ZetaValuesComplex
import PadicLFunctions.KubotaLeopoldt.MuA
import PadicLFunctions.KubotaLeopoldt.ZetaP
import PadicLFunctions.Coefficients
import PadicLFunctions.MeasureR.Basic
import PadicLFunctions.MeasureR.MahlerTransform
import PadicLFunctions.MeasureR.Convolution
import PadicLFunctions.MeasureR.Toolbox
import PadicLFunctions.MeasureR.UnitsZp
import PadicLFunctions.MeasureR.Fubini
import PadicLFunctions.MeasureR.UnitsRing
import PadicLFunctions.MeasureR.BaseChange
import PadicLFunctions.Interpolation.Characters
import PadicLFunctions.Interpolation.GenBernoulli
import PadicLFunctions.Interpolation.GenBernoulliComplex
import PadicLFunctions.Interpolation.Sawtooth
import PadicLFunctions.Interpolation.Twist
import PadicLFunctions.Interpolation.TameConductor
import PadicLFunctions.Interpolation.NonTame
import PadicLFunctions.Interpolation.Branches
import PadicLFunctions.PadicExp

/-!
# p-adic L-functions

A Lean 4 / Mathlib formalisation following

> J. Rodrigues Jacinto and C. Williams,
> *An introduction to p-adic L-functions*, arXiv:2309.15692.

The mathematical roadmap for the whole paper lives in the companion Verso
blueprint (`PadicLFunctionsBlueprint`). Individual results are laid down as
`sorry`-skeletons by `/develop` and discharged by `/beastmode`; the blueprint
dependency graph colours in automatically as the referenced declarations are
completed.
-/
