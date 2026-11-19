import LogicLineages.PersistentMarking.NumberedWindowRawWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowLiteralEqualityProof

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws
open Spine NumberedWindowSyntax NumberedWindowLiteralEquality
open NumberedWindowRawWitnessRootBits NumberedWindowRawWitnessTargets

theorem termEqTrue (Q R : NTerm) : termEq Q R = true ↔ Q = R :=
  NumberedWindowLiteralEqualityProof.term Q R

theorem argsEqTrue (qs rs : NArgs) : argsEq qs rs = true ↔ qs = rs :=
  NumberedWindowLiteralEqualityProof.args qs rs

theorem termRefl (Q : NTerm) : termEq Q Q = true := (termEqTrue Q Q).mpr rfl

theorem argsRefl (qs : NArgs) : argsEq qs qs = true := (argsEqTrue qs qs).mpr rfl

theorem resultTrue (o : Option NTerm) (R : NTerm) :
    resultBit o R = true ↔ o = some R := by
  cases o with
  | none => simp [resultBit]
  | some Q => simp only [resultBit,termEqTrue,Option.some.injEq]

theorem precedes : ExactPrecedenceBit := by
  intro S f g
  constructor
  · intro h
    cases hf : classRank S f with
    | none => simp [precedesBit,hf] at h
    | some m =>
      cases hg : classRank S g with
      | none => simp [precedesBit,hf,hg] at h
      | some n =>
        simp only [precedesBit,hf,hg,decide_eq_true_eq] at h
        exact ⟨m,n,hf,hg,h⟩
  · rintro ⟨m,n,hf,hg,h⟩
    simpa only [precedesBit,hf,hg,decide_eq_true_eq] using h

theorem equivalent : ExactEquivalentHeadBit := by
  intro S f g
  constructor
  · intro h
    cases hf : classRank S f with
    | none => simp [equivalentBit,hf] at h
    | some m =>
      cases hg : classRank S g with
      | none => simp [equivalentBit,hf,hg] at h
      | some n =>
        simp only [equivalentBit,hf,hg,decide_eq_true_eq] at h
        exact ⟨m,hf,hg.trans (congrArg some h.symm)⟩
  · rintro ⟨m,hf,hg⟩
    simp [equivalentBit,hf,hg]

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws
