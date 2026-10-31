module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerStageProof
public import Mathlib.Algebra.Colimit.DirectLimit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

instance walkerStageDirected (p : ℕ) (parent : WalkerParentSequence) :
    DirectedSystem (fun n => (walkerFinitePresentation p parent n).Carrier)
      (fun {n m} h => walkerStageMap p parent n m h) where
  map_self := by
    intro n x
    exact congrArg (fun f => f x) ((walker_stage_coherence p parent).1 n)
  map_map := by
    intro k m n hnm hmk x
    exact congrArg (fun f => f x) ((walker_stage_coherence p parent).2 n m k hnm hmk)

/-- Actual directed colimit of the explicitly constructed finite presentations.
The ordinal decreasing-node presentation is still a separate obligation. -/
abbrev WalkerSequentialGroup (p : ℕ) (parent : WalkerParentSequence) :=
  DirectLimit (fun n => (walkerFinitePresentation p parent n).Carrier) (walkerStageMap p parent)

noncomputable def walkerStageInclusion (p : ℕ) (parent : WalkerParentSequence) (n : ℕ) :
    (walkerFinitePresentation p parent n).Carrier →+ WalkerSequentialGroup p parent where
  toFun x := ⟦⟨n, x⟩⟧
  map_zero' := (DirectLimit.zero_def (f := walkerStageMap p parent) n).symm
  map_add' x y := (DirectLimit.add_def (f := walkerStageMap p parent) n x y).symm

noncomputable def walkerSequentialGenerator (p : ℕ) (parent : WalkerParentSequence) (i : ℕ) :
    WalkerSequentialGroup p parent :=
  walkerStageInclusion p parent (i+1) ((walkerFinitePresentation p parent (i+1)).generator (Fin.last i))

end LogicLineages.ModelsAlgebra.PGroups
