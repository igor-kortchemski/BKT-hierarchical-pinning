module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.FinalAssembly
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Profile
public import DiamondPinning.Proofs.ScalingCalculus
public import DiamondPinning.Proofs.ScalingCalculus4

/-!
# Helpers for the statements of `DiamondPinning.Statements.Scaling`

Owned helper module for the holes of `DiamondPinning.Statements.Scaling`
(Section 5 of the paper, with `cont:continuation`, proved in Section 7), which
imports it. It must not import any `DiamondPinning.Statements` module or the
Challenge.
-/
