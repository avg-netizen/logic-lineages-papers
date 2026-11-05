module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseSemanticProof
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
public import LogicLineages.OrdinalComparison.EncodedDescentProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientProof
open SemanticCoefficient Source.ForwardTranslation

 theorem exactNaturalValue : SemanticCoefficientTargets.ExactNaturalValue := by
  intro c k
  unfold Code.recognize
  dsimp only
  rw [encodedClosedPositiveCorrect c]
  cases ht : encodedFiniteTest (rawNoteEncode c.evaluate.1) with
  | false =>
    simp only [ht, Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
    intro he
    have hf : encodedFiniteTest (rawNoteEncode c.evaluate.1) = true :=
      (encodedFiniteCorrect c.evaluate).1.mpr (by rw [he]; exact Ordinal.natCast_lt_omega0 k)
    rw [ht] at hf
    contradiction
  | true =>
    simp only [ht, if_true, Option.some.injEq]
    have hv := (encodedFiniteCorrect c.evaluate).2 ht
    constructor
    · intro hk
      rw [← hv, hk]
    · intro hk
      exact_mod_cast hv.trans hk

theorem exactFiniteAcceptance : SemanticCoefficientTargets.ExactFiniteAcceptance := by
  intro c
  constructor
  · rintro ⟨k,hk⟩
    rw [(exactNaturalValue c k).mp hk]
    exact Ordinal.natCast_lt_omega0 k
  · intro h
    obtain ⟨k,hk⟩ := Ordinal.lt_omega0.mp h
    exact ⟨k,(exactNaturalValue c k).mpr hk⟩

theorem exactNonfiniteRejection : SemanticCoefficientTargets.ExactNonfiniteRejection := by
  intro c
  constructor
  · intro hn
    apply le_of_not_gt
    intro h
    obtain ⟨k,hk⟩ := (exactFiniteAcceptance c).mpr h
    rw [hn] at hk
    contradiction
  · intro h
    cases hr : Code.recognize (closedPositiveCode c) with
    | none => rfl
    | some k =>
      have hf := (exactFiniteAcceptance c).mp ⟨k,hr⟩
      exact False.elim ((not_lt_of_ge h) hf)

theorem positiveOutput : SemanticCoefficientTargets.PositiveOutput := by
  intro c k hk
  have hp := closedPositiveValuePositive c
  rw [(exactNaturalValue c k).mp hk] at hp
  exact_mod_cast hp

theorem structuralExtension : SemanticCoefficientTargets.StructuralExtension := by
  intro c k hk
  exact (exactNaturalValue c k).mpr (FiniteCoefficientBaseProof.actualCoefficient c k hk).2

theorem actualNumericProgram : SemanticCoefficientTargets.ActualNumericProgram := by
  have ht : Primrec (fun code => encodedFiniteTest (encodedClosedPositive code)) :=
    encodedFiniteAlgorithmsPrimitiveRecursive.1.comp encodedClosedPositivePrimitiveRecursive
  have hv : Primrec (fun code => encodedFiniteValue (encodedClosedPositive code)) :=
    (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).comp encodedClosedPositivePrimitiveRecursive
  apply (Primrec.cond ht (Primrec.option_some.comp hv) (Primrec.const none)).of_eq
  intro code
  unfold Code.recognize
  dsimp only
  cases he : encodedFiniteTest (encodedClosedPositive code) <;> simp [he]
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientProof
