import PadicLFunctions.Basic
import PadicLFunctions.Measure.Basic
import PadicLFunctions.Measure.MahlerTransform
import PadicLFunctions.Measure.Convolution
import PadicLFunctions.Measure.Toolbox
import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.Measure.Fubini
import PadicLFunctions.Measure.PseudoMeasure

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
