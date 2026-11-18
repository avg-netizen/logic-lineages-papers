module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerDefinitions
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming

open PlanCompiler (Instruction renameGateRaw)

abbrev RenameState := List Nat × List Nat × List Instruction

def liftTable (table : List Nat) : List Nat := 0 :: table.map Nat.succ

def renameStep (state : RenameState) (i : Instruction) : RenameState :=
  let (target,table,done) := state
  match i with
  | .inl (a,b) =>
      (target, table, .inl (Operations.renameCode target table a, Operations.renameCode target table b) :: done)
  | .inr (.inl g) =>
      (target, table, .inr (.inl (renameGateRaw table g)) :: done)
  | .inr (.inr _) =>
      (0 :: target, liftTable table, i :: done)

/-- Literal Plan renaming with the typed binder lift represented by its numeric table. -/
def renamePlanRaw (target table : List Nat) (code : List Instruction) : List Instruction :=
  (code.foldl renameStep (target,table,[])).2.2.reverse

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming
