module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HyperCloseBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion HyperCloseBlock

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

theorem programs : HyperCloseBlockTargets.Programs := by
  obtain ⟨hb1,hb2⟩ := HyperWindowProof.actualBoundPrograms
  refine ⟨hb1,hb2,?_⟩
  have hl : Primrec (fun q : Input => q.1.erase (HyperWindowCode.leftName q.2)) :=
    eraseP.comp (Primrec.fst.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
  have hr : Primrec (fun q : Input => q.1.erase (HyperWindowCode.rightName q.2)) :=
    eraseP.comp (Primrec.fst.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hc := HyperWindowCodeProof.actualCodeComputation
  have a := hl.to_comp.pair (hc.1.comp Computable.snd)
  have b := hr.to_comp.pair (hc.2.1.comp Computable.snd)
  have c := hl.to_comp.pair (hc.2.2.comp Computable.snd)
  exact Primrec.list_cons.to_comp.comp a
    (Primrec.list_cons.to_comp.comp b (Primrec.list_cons.to_comp.comp c (Computable.const [])))

theorem full : HyperCloseBlockTargets.Full :=
  ⟨actualAlternatives,pairElimination,blockPermutation,blockElimination,strictDecrease,literalCode,programs⟩
end LogicLineages.StandardControlCurrent.HyperCloseBlockProof
