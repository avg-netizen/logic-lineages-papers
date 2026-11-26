module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming

/-- Consume exactly one target index of the declared source type. -/
def scanEntry (target : List Nat) (remaining : Option (List Nat)) (sourceType : Nat) :
    Option (List Nat) :=
  match remaining with
  | some (i :: is) =>
    if RawValidator.«variable» target sourceType i then some is else none
  | _ => none

def tableGuard (source target table : List Nat) : Bool :=
  decide (source.foldl (scanEntry target) (some table) = some [])

def guard (target table : List Nat) (c : Code) : Bool :=
  valid c && tableGuard c.1 target table

/-- Check every free-context entry before applying the literal shared-table transformation. -/
def rename (target table : List Nat) (c : Code) : Option Code :=
  if guard target table c then some (Operations.renameCode target table c) else none

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming
