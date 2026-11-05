module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessScopeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
open LeastSourceWitness

theorem total_typed (values : List Nat) (i : Nat) (p : SourceFormula) :
    (search (values, i, p.encode)).Dom := by
  apply Nat.rfind_dom.mpr
  by_cases hn : need (values, i, p.encode) = true
  · have hp := need_admission values i p hn
    rcases (need_true_iff values i p hp).mp hn with ⟨n, hnbody⟩
    have ht := (body_truth values i p hp n).mpr hnbody
    refine ⟨n, ?_, ?_⟩
    · simp [hit, hn, ht]
    · intros; trivial
  · have hf : need (values, i, p.encode) = false := Bool.eq_false_iff.mpr hn
    refine ⟨0, ?_, ?_⟩
    · simp [hit, hf]
    · intros; trivial

theorem totalNumericSearch : LeastSourceWitnessTargets.TotalNumericSearch := by
  rintro ⟨values, i, code⟩
  have ht := total_typed values i (SourceFormulaCodec.decode code)
  simpa only [SourceFormulaCodecProof.codeRoundtrip code] using ht

theorem result_mem (p : Input) : result p ∈ search p := by
  classical
  unfold result
  rw [Part.getOrElse_of_dom _ (totalNumericSearch p)]
  exact Part.get_mem (totalNumericSearch p)

theorem result_eq_of_mem (p : Input) (n : Nat) (hn : n ∈ search p) : result p = n := by
  classical
  unfold result
  rw [Part.getOrElse_of_dom _ (totalNumericSearch p)]
  exact Part.get_eq_of_mem hn (totalNumericSearch p)

theorem exactNumericStatus : LeastSourceWitnessTargets.ExactNumericStatus := by
  intro p
  constructor
  · cases hn : need p <;> simp [witness, hn]
  · intro hn
    apply result_eq_of_mem p 0
    apply Nat.mem_rfind.mpr
    constructor
    · simp [hit, hn]
    · intro m hm; omega

theorem witness_some_iff (p : Input) (n : Nat) :
    witness p = some n ↔ need p = true ∧ n ∈ search p := by
  by_cases hn : need p = true
  · rw [witness, if_pos hn]
    simp only [Option.some.injEq, hn, true_and]
    constructor
    · intro h; rw [← h]; exact result_mem p
    · exact result_eq_of_mem p n
  · simp [witness, hn]

theorem actualLeastWitness : LeastSourceWitnessTargets.ActualLeastWitness := by
  intro values i p hp n
  rw [witness_some_iff]
  constructor
  · rintro ⟨hn, hs⟩
    have hs' := Nat.mem_rfind.mp hs
    have ht : FiniteSearchPrograms.Code.answer (BoundedSourcePrograms.Code.update values i n) p.encode = true := by
      simpa [hit, hn] using hs'.1
    refine ⟨(body_truth values i p hp n).mp ht, ?_⟩
    intro m hm hmbody
    have hfalse := hs'.2 hm
    have htrue := (body_truth values i p hp m).mpr hmbody
    simp [hit, hn, htrue] at hfalse
  · rintro ⟨hnbody, hmin⟩
    have hn : need (values, i, p.encode) = true := (need_true_iff values i p hp).mpr ⟨n, hnbody⟩
    refine ⟨hn, Nat.mem_rfind.mpr ⟨?_, ?_⟩⟩
    · have ht := (body_truth values i p hp n).mpr hnbody
      simp [hit, hn, ht]
    · intro m hm
      have ht : FiniteSearchPrograms.Code.answer (BoundedSourcePrograms.Code.update values i m) p.encode = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hmin m hm ((body_truth values i p hp m).mp hh)
      simp [hit, hn, ht]

theorem actualNoWitness : LeastSourceWitnessTargets.ActualNoWitness := by
  intro values i p hp
  have hn := need_true_iff values i p hp
  by_cases h : need (values, i, p.encode) = true
  · simp [witness, h, hn.mp h]
  · have he : ¬(SourceFormula.existsNat i p).eval (PlainParameterDecision.valuation values) := by
      intro hh; exact h (hn.mpr hh)
    simp [witness, h, he]

theorem actualRawWitness : LeastSourceWitnessTargets.ActualRawWitness := by
  intro values i code hp n
  let p := SourceFormulaCodec.decode code
  have hc : p.encode = code := SourceFormulaCodecProof.codeRoundtrip code
  have ht : FiniteSearchSource.test (.existsNat i p) = true := by
    rw [← FiniteSearchProgramsProof.literalSyntaxCode (.existsNat i p)]
    simpa only [SourceFormula.encode, hc, parent] using hp
  have h := actualLeastWitness values i p ht n
  simpa only [hc] using h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
