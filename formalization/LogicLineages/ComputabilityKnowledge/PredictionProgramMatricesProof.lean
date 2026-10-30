module

public import LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesProof
open PredictionLearning PredictionCanonicalList PredictionProgramMatrices PredictionProgramMatricesTargets

theorem primitiveRecursiveTotalMatrix : PrimitiveRecursiveTotalMatrix :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.snd.comp Primrec.snd).pair Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))

theorem exactTotalityMatrix : ExactTotalityMatrix := by
  intro c
  constructor
  · intro hc input
    obtain ⟨v, hv⟩ := hc input
    obtain ⟨fuel, hf⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    exact ⟨fuel, by simp [totalMatrix, Option.mem_def.mp hf]⟩
  · intro h input
    obtain ⟨fuel, hf⟩ := h input
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hf
    exact ⟨v, Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)⟩

private theorem pr_agreement : Primrec (fun z : Option Nat × Option Nat => observedAgreement z.1 z.2) := by
  apply (Primrec.option_casesOn Primrec.fst (Primrec.const true)
    ((Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)).decide).to₂).of_eq
  intro z
  cases z.1 <;> rfl

theorem primitiveRecursiveEqualityMatrix : PrimitiveRecursiveEqualityMatrix := by
  let D := (Code × Code) × Nat × Nat
  have hc : Primrec (fun z : D => z.1.1) := Primrec.fst.comp Primrec.fst
  have hd : Primrec (fun z : D => z.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : D => z.2.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hs : Primrec (fun z : D => z.2.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have ht : Primrec (fun z : D => z.2.2) := Primrec.snd.comp Primrec.snd
  have hcs := Nat.Partrec.Code.primrec_evaln.comp ((hs.pair hc).pair hi)
  have hds := Nat.Partrec.Code.primrec_evaln.comp ((hs.pair hd).pair hi)
  have hct := Nat.Partrec.Code.primrec_evaln.comp ((ht.pair hc).pair hi)
  have hdt := Nat.Partrec.Code.primrec_evaln.comp ((ht.pair hd).pair hi)
  exact Primrec.and.comp (pr_agreement.comp (hcs.pair hdt)) (pr_agreement.comp (hds.pair hct))

private theorem eventual_agreement (c d : Code) (heq : SameFunction c d) (input stage : Nat) :
    ∃ T, ∀ t, T ≤ t → observedAgreement (Nat.Partrec.Code.evaln stage c input)
      (Nat.Partrec.Code.evaln t d input) = true := by
  cases ho : Nat.Partrec.Code.evaln stage c input with
  | none => exact ⟨0, fun _ _ => rfl⟩
  | some v =>
      have hv := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr ho)
      rw [heq input] at hv
      obtain ⟨T, hT⟩ := Nat.Partrec.Code.evaln_complete.mp hv
      refine ⟨T, fun t ht => ?_⟩
      have hm := Option.mem_def.mp (Nat.Partrec.Code.evaln_mono ht hT)
      simp only [observedAgreement, hm, decide_true]

theorem exactExtensionalEqualityMatrix : ExactExtensionalEqualityMatrix := by
  intro c d
  constructor
  · intro heq query
    obtain ⟨T, hT⟩ := eventual_agreement c d heq query.unpair.1 query.unpair.2
    obtain ⟨U, hU⟩ := eventual_agreement d c (fun n => (heq n).symm) query.unpair.1 query.unpair.2
    exact ⟨max T U, by simp only [equalityMatrix, hT _ (le_max_left _ _), hU _ (le_max_right _ _), Bool.and_self]⟩
  · intro h input
    apply Part.ext
    intro v
    constructor
    · intro hv
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
      obtain ⟨t, ht⟩ := h (Nat.pair input s)
      have hh : observedAgreement (Nat.Partrec.Code.evaln s c input)
          (Nat.Partrec.Code.evaln t d input) = true := by
        simp only [equalityMatrix, Nat.unpair_pair, Bool.and_eq_true] at ht
        exact ht.1
      have hm : Nat.Partrec.Code.evaln t d input = some v := by
        simpa only [Option.mem_def.mp hs, observedAgreement, decide_eq_true_eq] using hh
      exact Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hm)
    · intro hv
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
      obtain ⟨t, ht⟩ := h (Nat.pair input s)
      have hh : observedAgreement (Nat.Partrec.Code.evaln s d input)
          (Nat.Partrec.Code.evaln t c input) = true := by
        simp only [equalityMatrix, Nat.unpair_pair, Bool.and_eq_true] at ht
        exact ht.2
      have hm : Nat.Partrec.Code.evaln t c input = some v := by
        simpa only [Option.mem_def.mp hs, observedAgreement, decide_eq_true_eq] using hh
      exact Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hm)

end LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesProof
