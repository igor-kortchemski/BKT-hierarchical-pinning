module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Instance pins for the frozen statements

The frozen statements (`DiamondPinning.Statements.*`) and the Challenge must
elaborate to the same terms. A Bochner integral `∫ x, f x ∂μ` of a real
function needs an instance of `NormedSpace ℝ ℝ`; with only the Challenge's
Mathlib imports it is `NormedField.toNormedSpace`, while larger imports (inner
product spaces, `RCLike`) make Lean find the propositionally equal
`InnerProductSpace.toNormedSpace` first. Raising the priority of
`NormedField.toNormedSpace` makes every module importing this one, the
frozen statement modules included, choose the same instance as the
Challenge. This is only a choice between equal instances; it changes no
statement. The owned helper modules imported by the frozen statement modules
import this module.
-/

attribute [instance high] NormedField.toNormedSpace
