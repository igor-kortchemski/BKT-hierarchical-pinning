module

public import DiamondPinning.Model.Defs
public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.FreeEnergy

/-!
# Helpers for the frozen `lem:basic-bounds` statements

Owned helper module for the five holes `integrable_lawR`,
`integrable_tiltedLogPower`, `integrable_log_lawR`, `freeEnergy_tendsto` and
`criticalPoint_isGreatest` of `DiamondPinning.Statements.Main`, which imports
it. It must not import `DiamondPinning.Statements.Main` or the Challenge.
-/
