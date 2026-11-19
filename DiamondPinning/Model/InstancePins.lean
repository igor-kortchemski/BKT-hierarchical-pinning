module

public import Mathlib.Analysis.Normed.Module.Basic

/-! # A consistent normed-space instance for Bochner integrals

The statements (`DiamondPinning.Statements.*`) and the Challenge use the same
normed-space instance. A Bochner integral `∫ x, f x ∂μ` of a real function
needs an instance of `NormedSpace ℝ ℝ`; with only the Challenge's Mathlib
imports it is `NormedField.toNormedSpace`, while larger imports (inner product
spaces, `RCLike`) make Lean find the propositionally equal
`InnerProductSpace.toNormedSpace` first. Raising the priority of
`NormedField.toNormedSpace` makes every module importing this one choose the
same instance as the Challenge. This is only a choice between equal instances;
it changes no mathematical statement.
-/

attribute [instance high] NormedField.toNormedSpace
