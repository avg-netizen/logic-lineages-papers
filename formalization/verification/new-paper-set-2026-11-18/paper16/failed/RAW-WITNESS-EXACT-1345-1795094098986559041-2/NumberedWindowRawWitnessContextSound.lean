import LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSimpleSound
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSound

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSound
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessLaws NumberedWindowRawWitnessTargets

private theorem numberedBase {S K i w}
    (ih : ∀ Q R, rawBit S K w Q R = true → RawStep S K Q R) :
    ∀ Q R, rawBit S K (.numberedBase i w) Q R = true → RawStep S K Q R := by
  intro Q R h
  cases Q <;> try (simp only [rawBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case numbered g ρ l bt et =>
      change (decide (f = g) && decide (τ = ρ) && decide (k = l) && argsEq es et &&
        argsAtBit (rawBit S K w) i bs bt) = true at h
      simp only [Bool.and_eq_true,decide_eq_true_eq,argsEqTrue] at h
      rcases h with ⟨⟨⟨⟨ef,eτ⟩,ek⟩,ee⟩,hb⟩
      subst g
      subst ρ
      subst l
      subst et
      exact .numberedBase (NumberedWindowRawWitnessContextSimpleSound.argsAt ih i _ _ hb)

private theorem numberedExtra {S K i w}
    (ih : ∀ Q R, rawBit S K w Q R = true → RawStep S K Q R) :
    ∀ Q R, rawBit S K (.numberedExtra i w) Q R = true → RawStep S K Q R := by
  intro Q R h
  cases Q <;> try (simp only [rawBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case numbered g ρ l bt et =>
      change (decide (f = g) && decide (τ = ρ) && decide (k = l) && argsEq bs bt &&
        argsAtBit (rawBit S K w) i es et) = true at h
      simp only [Bool.and_eq_true,decide_eq_true_eq,argsEqTrue] at h
      rcases h with ⟨⟨⟨⟨ef,eτ⟩,ek⟩,eb⟩,he⟩
      subst g
      subst ρ
      subst l
      subst bt
      exact .numberedExtra (NumberedWindowRawWitnessContextSimpleSound.argsAt ih i _ _ he)

theorem term (S : Signature) (K : List Ty) :
    ∀ w Q R, rawBit S K w Q R = true → RawStep S K Q R := by
  intro w
  induction w with
  | root w => intro Q R h; exact NumberedWindowRawWitnessRootSound.sound h
  | lam w ih => exact NumberedWindowRawWitnessContextSimpleSound.lam ih
  | ordinaryBase i w ih => exact NumberedWindowRawWitnessContextSimpleSound.ordinaryBase ih
  | numberedBase i w ih => exact numberedBase ih
  | numberedExtra i w ih => exact numberedExtra ih
  | auxFunction w ih => exact NumberedWindowRawWitnessContextSimpleSound.auxFunction ih

theorem args (S : Signature) (K : List Ty) (i : Nat) (w : RawWitness) :
    ∀ qs rs, argsAtBit (rawBit S K w) i qs rs = true → RawArgsStep S K qs rs :=
  NumberedWindowRawWitnessContextSimpleSound.argsAt (term S K w) i

theorem supplied : SuppliedRawWitnessSound := ⟨term,args⟩

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSound
