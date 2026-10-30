module

public import LogicLineages.ComputabilityKnowledge.OraclePiTwoTargets
public import LogicLineages.ComputabilityKnowledge.OracleJumpProof
public import LogicLineages.ComputabilityKnowledge.OracleUniversalProof
public import LogicLineages.ComputabilityKnowledge.OracleProgramProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiTwoProof
open OracleProgram OracleUniversal OracleJump OraclePiTwo OracleRelativeRecursion OraclePiTwoTargets

private theorem zero_search_dom (test : Nat → Nat) (input : Nat) :
    (zeroSearch test input).Dom ↔ ∃ n, test (Nat.pair input n) = 0 := by
  constructor
  · intro h
    obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp h
    exact ⟨n, of_decide_eq_true (Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n, hn⟩
    exact Nat.rfind_dom.mpr ⟨n, by simp [hn], fun {_} _ => trivial⟩

theorem ordinaryWitnessCompiler : OrdinaryWitnessCompiler := by
  intro matrix hm
  have hq : Primrec (fun z : Nat => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hx : Primrec (fun z : Nat => z.unpair.1.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hq)
  have hi : Primrec (fun z : Nat => z.unpair.1.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hq)
  have hy : Primrec (fun z : Nat => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have ht : Primrec (witnessTest matrix) := by
    apply (Primrec.cond (hm.comp (hi.pair (hx.pair hy))) (Primrec.const 0) (Primrec.const 1)).of_eq
    intro z
    unfold witnessTest
    cases matrix (z.unpair.1.unpair.1, z.unpair.1.unpair.2, z.unpair.2) <;> rfl
  have hr : RecursiveIn ∅ (witnessSearch matrix) :=
    OracleRelativeRecursionProof.relativePartialSearch ∅ _ ht.computableIn
  have hp : Partrec (witnessSearch matrix) := recursiveIn_empty_iff.mp hr
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hp)
  refine ⟨code, fun query => congrFun hc query, ?_⟩
  intro i x
  rw [congrFun hc (Nat.pair i x)]
  change (zeroSearch _ _).Dom ↔ _
  rw [zero_search_dom]
  simp [witnessTest]

private theorem pr_counterQuery (code : Nat.Partrec.Code) : Primrec (counterQuery code) :=
  OracleJumpProof.ordinaryToFirstCalibration.1.comp
    (Primrec₂.natPair.comp (Primrec.const (Encodable.encode code)) Primrec.id)

theorem relativeCounterSearch : RelativeCounterSearch := by
  intro code
  have ho : ComputableIn {fun n => Part.some (firstJump n)} firstJump :=
    RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ rfl)
  have ht := OracleRelativeRecursionProof.relativeComposition _ _ _ ho (pr_counterQuery code).computableIn
  exact OracleRelativeRecursionProof.relativePartialSearch _ _ ht

theorem exactCounterSearchDomain : ExactCounterSearchDomain := by
  classical
  intro matrix code hc i
  rw [counterSearch, zero_search_dom]
  apply exists_congr
  intro x
  change firstJump (ordinaryToFirst (Nat.pair (Encodable.encode code) (Nat.pair i x))) = 0 ↔ _
  rw [OracleJumpProof.ordinaryToFirstCalibration.2]
  simp only [ordinaryIndicator, ordinaryHalting, Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h : ∃ y, matrix (i, x, y) = true
  · rw [if_pos ((hc i x).mpr h)]
    constructor
    · intro hz; cases hz
    · intro hf
      obtain ⟨y, hy⟩ := h
      rw [hf y] at hy
      contradiction
  · have hd : ¬(code.eval (Nat.pair i x)).Dom := fun hd => h ((hc i x).mp hd)
    rw [if_neg hd]
    constructor
    · intro _ y
      exact Bool.eq_false_iff.mpr (fun hy => h ⟨y, hy⟩)
    · intro _; rfl

theorem actualPiTwoSecondJumpDecision : ActualPiTwoSecondJumpDecision := by
  classical
  intro matrix hm
  obtain ⟨code, _, hc⟩ := ordinaryWitnessCompiler matrix hm
  obtain ⟨p, hp⟩ := OracleProgramProof.oracleEvaluationComplete
    (fun n => Part.some (firstJump n)) (counterSearch code)
    (RecursiveIn.iff_nat.mp (relativeCounterSearch code))
  have he : ∀ i, universal firstJump (Nat.pair (encode p) i) = counterSearch code i := by
    intro i
    apply Part.ext
    intro output
    rw [OracleUniversalProof.encodedUniversalSemantics, hp]
  have hquery : Primrec (fun i => Nat.pair (encode p) i) :=
    Primrec₂.natPair.comp (Primrec.const _) Primrec.id
  have ho : ComputableIn {fun n => Part.some (secondJump n)} secondJump :=
    RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ rfl)
  have hvalue := OracleRelativeRecursionProof.relativeComposition _ _ _ ho hquery.computableIn
  have hneg := OracleRelativeRecursionProof.relativeComposition _ _ _
    (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).computableIn hvalue
  apply hneg.of_eq
  intro i
  change Part.some (1 - secondJump (Nat.pair (encode p) i)) = Part.some (matrixIndicator matrix i)
  congr 1
  simp only [secondJump, jump, he, matrixIndicator]
  rw [exactCounterSearchDomain matrix code hc i]
  by_cases h : ∀ x, ∃ y, matrix (i, x, y) = true
  · have hn : ¬∃ x, ∀ y, matrix (i, x, y) = false := by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := h x
      rw [hx y] at hy
      contradiction
    simp [h, hn]
  · have hn : ∃ x, ∀ y, matrix (i, x, y) = false := by
      push_neg at h
      obtain ⟨x, hx⟩ := h
      exact ⟨x, fun y => Bool.eq_false_iff.mpr (hx y)⟩
    simp [h, hn]

end LogicLineages.ComputabilityKnowledge.OraclePiTwoProof
