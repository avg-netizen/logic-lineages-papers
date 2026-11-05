module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessSearchProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsAnswerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
open LeastSourceWitness
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem parent_primitive : Primrec parent :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))) (Primrec.const 4)

theorem need_computable : Computable need :=
  (show PrimrecRel (fun a b : Option Bool => a = b) from Primrec.eq).decide.to_comp.comp
    (FiniteSearchProgramsProof.decide_computable.comp Computable.fst parent_primitive.to_comp) (Computable.const (some true))

theorem hit_computable : Computable₂ hit := by
  have hu : Computable (fun p : Input × Nat => BoundedSourcePrograms.Code.update p.1.1 p.1.2.1 p.2) :=
    BoundedSourceProgramsProof.update_primitive.to_comp.comp
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have ha : Computable (fun p : Input × Nat =>
      FiniteSearchPrograms.Code.answer (BoundedSourcePrograms.Code.update p.1.1 p.1.2.1 p.2) p.1.2.2) :=
    FiniteSearchProgramsProof.answer_computable.comp hu (Computable.snd.comp (Computable.snd.comp Computable.fst))
  exact Primrec.or.to_comp.comp (Primrec.not.to_comp.comp (need_computable.comp Computable.fst)) ha

theorem search_partrec : Partrec search := Partrec.rfind hit_computable.partrec₂

/-- Global search termination proves that the fixed totalization is the same
actual partial-recursive program, rather than adding a termination premise. -/
theorem result_computable : Computable result := by
  change Partrec (fun p => Part.some (result p))
  apply search_partrec.of_eq
  intro p
  exact Part.eq_some_iff.mpr (result_mem p)

theorem witness_computable : Computable witness := by
  apply (Computable.cond need_computable (Computable.option_some.comp result_computable) (Computable.const none)).of_eq
  intro p
  unfold witness
  cases need p <;> rfl

theorem actualNumericPrograms : LeastSourceWitnessTargets.ActualNumericPrograms :=
  ⟨parent_primitive.to_comp, need_computable, hit_computable, search_partrec, result_computable, witness_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
