module
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperCodeProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion MixedRunnerBlock

private theorem eraseP : Primrec (fun q : List Nat × Nat => q.1.erase q.2) := by
  have hs : Primrec₂ (fun q : List Nat × Nat => fun step : Nat × List Nat × List Nat =>
      if step.1=q.2 then step.2.1 else step.1::step.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  apply (Primrec.list_rec Primrec.fst (Primrec.const []) hs).of_eq
  intro q
  induction q.1 with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.erase_cons,beq_iff_eq,ih]

theorem literalCode : MixedRunnerBlockTargets.LiteralCode := by
  refine ⟨?_,?_,?_⟩
  · intro xs i anchor e c p
    unfold reverseProgram
    rw [ReverseWindowCodeProof.literalCodeCalibration]
    rfl
  · intro xs i j lk rk e h k l a p
    unfold linearProgram
    rw [LinearWindowCodeProof.literalCodeCalibration]
    rfl
  · intro xs i j kind e h k l q a p
    unfold activeProgram
    rw [ActiveHyperCodeProof.literalCodeCalibration]
    rfl

theorem programs : MixedRunnerBlockTargets.Programs := by
  refine ⟨LinearWindowProof.actualBoundProgram,ActiveHyperProof.actualBoundProgram,?_,?_,?_⟩
  · have he : Primrec (fun q : ReverseInput => q.1.erase q.2.1) :=
      eraseP.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
    exact he.to_comp.pair (ReverseWindowCodeProof.actualCodeComputation.comp Computable.snd)
  · have he : Primrec (fun q : LinearInput => q.1.erase (LinearWindow.Code.rightName q.2)) :=
      eraseP.comp (Primrec.fst.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact he.to_comp.pair (LinearWindowCodeProof.actualCodeComputation.comp Computable.snd)
  · have he : Primrec (fun q : ActiveInput => q.1.erase (ActiveHyper.Code.rightName q.2)) :=
      eraseP.comp (Primrec.fst.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact he.to_comp.pair (ActiveHyperCodeProof.actualCodeComputation.comp Computable.snd)

theorem full : MixedRunnerBlockTargets.Full :=
  ⟨reverseWitness,reverseElimination,reverseBlock,linearBounds,linearElimination,linearBlock,
   activeBounds,activeElimination,activeBlock,literalCode,programs⟩
end LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
