module
public import LogicLineages.StandardControlCurrent.InverseBoundaryBlockProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseBoundaryBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open InverseBoundaryBlock

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

theorem literalCode : InverseBoundaryBlockTargets.LiteralCode := by
  intro xs i a shift lower upper p
  change (xs.erase i,DominantBoundary.Code.project (i,a,shift,lower.encode,upper.encode,p.encode)) = _
  rw [DominantBoundaryProof.project_calibration]
  rfl

theorem programs : InverseBoundaryBlockTargets.Programs := by
  have he : Primrec (fun q : Input => q.1.erase q.2.1) :=
    eraseP.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  exact he.to_comp.pair (DominantBoundaryProof.actualNumericProgram.comp Computable.snd)

theorem full : InverseBoundaryBlockTargets.Full :=
  ⟨actualBand,singleElimination,blockElimination,progressSupport,literalCode,programs⟩
end LogicLineages.StandardControlCurrent.InverseBoundaryBlockProof
