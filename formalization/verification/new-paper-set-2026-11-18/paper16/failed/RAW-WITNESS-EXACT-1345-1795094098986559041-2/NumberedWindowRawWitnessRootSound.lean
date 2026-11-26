import LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSimpleSound
import LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationProof

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSound
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessRootBits NumberedWindowRawWitnessLaws
open NumberedWindowHeadEnumerationTargets (headBit)
open NumberedWindowPrimitiveWitnessBits (replacementBit)

private theorem select {S K ex i ds Q R} (h : rootBit S K (.select ex i ds) Q R = true) :
    RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases k with
    | zero => simp only [rootBit,Bool.false_eq_true] at h
    | succ k =>
      cases hg : (if ex then es else bs).get i with
      | none => simp only [rootBit,hg,Bool.false_eq_true] at h
      | some selected =>
        simp only [rootBit,hg,Bool.and_eq_true,decide_eq_true_eq,resultTrue] at h
        have get : bs.get i = some selected ∨ es.get i = some selected := by
          cases ex with
          | false => exact Or.inl hg
          | true => exact Or.inr hg
        exact .select get h.1 h.2

private theorem copy {S K Q R} (h : rootBit S K .copy Q R = true) : RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases k with
    | zero => simp only [rootBit,Bool.false_eq_true] at h
    | succ k =>
      cases R <;> try (simp only [rootBit,Bool.false_eq_true] at h)
      case ordinary g target =>
        change (decide (τ = g.result) && precedesBit S f g && headBit S K g &&
          argsEq (ownerCopies f k bs es g.arguments) target) = true at h
        simp only [Bool.and_eq_true,decide_eq_true_eq,precedes S f g,
          NumberedWindowHeadEnumerationProof.bit S K g,argsEqTrue] at h
        rcases h with ⟨⟨⟨et,hp⟩,hg⟩,e⟩
        subst τ
        subst target
        exact .copy hp hg

private theorem stat {S K part Q R} (h : rootBit S K (.stat part) Q R = true) :
    RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases k with
    | zero => simp only [rootBit,Bool.false_eq_true] at h
    | succ k =>
      cases R <;> try (simp only [rootBit,Bool.false_eq_true] at h)
      case ordinary g target =>
        change (decide (τ = g.result) && equivalentBit S f g && headBit S K g &&
          replacementBit bs target part) = true at h
        simp only [Bool.and_eq_true,decide_eq_true_eq,equivalent S f g,
          NumberedWindowHeadEnumerationProof.bit S K g] at h
        rcases h with ⟨⟨⟨et,he⟩,hg⟩,hp⟩
        have partOk := (NumberedWindowPrimitiveWitnessChecks.exact_CertifiedPrimitiveReplacement
          bs target).mp ⟨part,hp⟩
        subst τ
        exact .stat he hg partOk

theorem sound {S K w Q R} (h : rootBit S K w Q R = true) : RawStep S K Q R := by
  cases w with
  | mark k => exact NumberedWindowRawWitnessRootSimpleSound.mark h
  | lower => exact NumberedWindowRawWitnessRootSimpleSound.lower h
  | select => exact select h
  | copy => exact copy h
  | stat => exact stat h
  | fabs => exact NumberedWindowRawWitnessRootSimpleSound.fabs h
  | beta => exact NumberedWindowRawWitnessRootSimpleSound.beta h
  | bottom => exact NumberedWindowRawWitnessRootSimpleSound.bottom h

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSound
