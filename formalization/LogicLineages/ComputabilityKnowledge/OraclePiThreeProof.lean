module

public import LogicLineages.ComputabilityKnowledge.OraclePiThreeTargets
public import LogicLineages.ComputabilityKnowledge.OraclePiTwoProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiThreeProof
open OracleProgram OracleUniversal OracleJump OracleRelativeRecursion OraclePiThree OraclePiThreeTargets

private theorem counter_value (R : Matrix) (i x : Nat) :
    counterIndicator R (Nat.pair i x) = 1 ↔ ∀ y, ∃ z, R (i, x, y, z) = false := by
  classical
  simp [counterIndicator, OraclePiTwo.matrixIndicator, counterMatrix]

theorem counterMatrixCalibration : CounterMatrixCalibration := by
  intro R hR
  refine ⟨?_, counter_value R⟩
  have hi : Primrec (fun a : Nat × Nat × Nat => a.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hx : Primrec (fun a : Nat × Nat × Nat => a.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  exact Primrec.not.comp (hR.comp
    (hi.pair (hx.pair ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))))

theorem relativePiThreeCounterSearch : RelativePiThreeCounterSearch := by
  intro R hR
  have hcounter : ComputableIn {fun n => Part.some (secondJump n)} (counterIndicator R) :=
    OraclePiTwoProof.actualPiTwoSecondJumpDecision (counterMatrix R) (counterMatrixCalibration R hR).1
  have htest := OracleRelativeRecursionProof.relativeComposition _ _ _
    (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).computableIn hcounter
  exact OracleRelativeRecursionProof.relativePartialSearch _ _ htest

private theorem zero_search_dom (test : Nat → Nat) (input : Nat) :
    (zeroSearch test input).Dom ↔ ∃ n, test (Nat.pair input n) = 0 := by
  constructor
  · intro h
    obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp h
    exact ⟨n, of_decide_eq_true (Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n, hn⟩
    exact Nat.rfind_dom.mpr ⟨n, by simp [hn], fun {_} _ => trivial⟩

theorem exactPiThreeCounterDomain : ExactPiThreeCounterDomain := by
  classical
  intro R i
  rw [counterSearch, zero_search_dom]
  apply exists_congr
  intro x
  simp only [counterTest, counterIndicator, OraclePiTwo.matrixIndicator, counterMatrix, Nat.unpair_pair, Bool.not_eq_true]
  split_ifs <;> simp_all

theorem actualPiThreeThirdJumpDecision : ActualPiThreeThirdJumpDecision := by
  classical
  intro R hR
  obtain ⟨p, hp⟩ := OracleProgramProof.oracleEvaluationComplete
    (fun n => Part.some (secondJump n)) (counterSearch R)
    (RecursiveIn.iff_nat.mp (relativePiThreeCounterSearch R hR))
  have he : ∀ i, universal secondJump (Nat.pair (encode p) i) = counterSearch R i := by
    intro i
    apply Part.ext
    intro output
    rw [OracleUniversalProof.encodedUniversalSemantics, hp]
  have hquery : Primrec (fun i => Nat.pair (encode p) i) :=
    Primrec₂.natPair.comp (Primrec.const _) Primrec.id
  have ho : ComputableIn {fun n => Part.some (thirdJump n)} thirdJump :=
    RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ rfl)
  have hvalue := OracleRelativeRecursionProof.relativeComposition _ _ _ ho hquery.computableIn
  have hneg := OracleRelativeRecursionProof.relativeComposition _ _ _
    (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).computableIn hvalue
  apply hneg.of_eq
  intro i
  change Part.some (1 - thirdJump (Nat.pair (encode p) i)) = Part.some (matrixIndicator R i)
  congr 1
  simp only [thirdJump, jump, he, matrixIndicator]
  rw [exactPiThreeCounterDomain R i]
  by_cases h : ∀ x, ∃ y, ∀ z, R (i, x, y, z) = true
  · have hn : ¬∃ x, ∀ y, ∃ z, R (i, x, y, z) = false := by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := h x
      obtain ⟨z, hz⟩ := hx y
      rw [hy z] at hz
      contradiction
    simp [h, hn]
  · have hn : ∃ x, ∀ y, ∃ z, R (i, x, y, z) = false := by
      push_neg at h
      obtain ⟨x, hx⟩ := h
      exact ⟨x, fun y => by obtain ⟨z, hz⟩ := hx y; exact ⟨z, Bool.eq_false_iff.mpr hz⟩⟩
    simp [h, hn]

end LogicLineages.ComputabilityKnowledge.OraclePiThreeProof
