module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence

open LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG (Code)

def counterexample {Γ : List Ty} (weakQuery : Bool) (a b : Input Γ .ground) :
    InputNormalization.Input Γ 0 :=
  .observation a (.observation (ScopedDAG.renameInput (Renaming.weaken Γ .ground) b)
    (.boolean (if weakQuery then .lt (.var .here) (.var (.there .here))
      else .le (.var .here) (.var (.there .here))) (.finish 0)))

def counterexampleCode (weakQuery : Bool) (n : Nat) (a b : Code) :
    RawSourceDAG.InputCompiler.InputCode :=
  let ctx := List.replicate n 0
  let b' := RawSourceDAG.Operations.renameCode (0 :: ctx) (RawSourceDAG.BinaryPlanCompiler.prefixTable 1 ctx) b
  ([((8,0,0),some a),((8,0,0),some b'),((if weakQuery then 2 else 1,1,2),none)],0)

def reduce (weakQuery : Bool) (n : Nat) (a b : Code) : Code × Code :=
  let out := CurrentCompiler.compile (n,counterexampleCode weakQuery n a b)
  if weakQuery then out.1 else out.2

end LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence
