module

public import DiamondPinning.Model.Defs
public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.FinalAssembly

/-!
# Helpers for the frozen statement `bkt`

Owned helper module for the hole `bkt` of `DiamondPinning.Statements.Main`,
which imports it: the final assembly of Theorem `th:bkt` from the
development. It must not import `DiamondPinning.Statements.Main` or the
Challenge.
-/
