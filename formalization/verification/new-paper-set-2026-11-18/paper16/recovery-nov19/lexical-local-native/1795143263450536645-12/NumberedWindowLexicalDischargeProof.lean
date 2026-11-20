import LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowLexicalDischargeProof
open Spine NumberedWindowArithmeticTyCode NumberedWindowLexicalAlgorithm NumberedWindowArithmeticLexicalTargets

theorem codeInj {s t : Ty} (h : encodeTy s = encodeTy t) : s = t := by
  have k := congrArg decodeTy h
  simpa only [NumberedWindowArithmeticAtomCodeChecks.exact_TyCodec.2.1,
    Option.some.injEq] using k

theorem codeEq (s t : Ty) : (encodeTy s == encodeTy t) = decide (s = t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  exact ⟨codeInj,congrArg encodeTy⟩

theorem listEq (ss ts : List Ty) : (ss.map encodeTy == ts.map encodeTy) = decide (ss = ts) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  exact List.map_inj_right (fun _ _ h => codeInj h)

theorem boundEq (C : BoundContext) (i : Nat) (σ : Ty) :
    (codeLookup C i == some (encodeTy σ)) = decide (C i = some σ) := by
  unfold codeLookup
  cases h : C i with
  | none => rfl
  | some t =>
    apply Bool.eq_iff_iff.mpr
    simp only [Option.map_some,beq_iff_eq,Option.some.injEq,decide_eq_true_eq]
    exact ⟨codeInj,congrArg encodeTy⟩

theorem holdsJoin (C : Nat → Option Nat) (a b : Requirement) :
    holds C (join a b) = (holds C a && holds C b) := by
  simp [holds,join,List.all_append,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

theorem holdsRestrict (C : Nat → Option Nat) (ok : Bool) (r : Requirement) :
    holds C (restrict ok r) = (ok && holds C r) := by simp [holds,restrict,Bool.and_assoc]

theorem holdsSlot (C : Nat → Option Nat) (i t : Nat) :
    holds C (slot i t) = (C i == some t) := by simp [holds,slot]

private def pushCode (C : Nat → Option Nat) (t : Nat) : Nat → Option Nat
  | 0 => some t
  | i+1 => C i

private theorem dischargeSpec (C : Nat → Option Nat) (t : Nat) (rs : List (Nat × Nat)) :
    holds C (discharge t rs) = rs.all (fun p => pushCode C t p.1 == some p.2) := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨_ | i,u⟩
    · simp [discharge,holdsRestrict,ih,pushCode]
      have sym : (u == t) = (t == u) := Bool.eq_iff_iff.mpr (by simp [eq_comm])
      rw [sym]
    · simp [discharge,holdsJoin,holdsSlot,ih,pushCode]

theorem holdsBinder (C : BoundContext) (σ : Ty) (r : Requirement) :
    holds (codeLookup C) (binder (encodeTy σ) r) = holds (codeLookup (C.push σ)) r := by
  have same : pushCode (codeLookup C) (encodeTy σ) = codeLookup (C.push σ) := by
    funext i
    cases i <;> rfl
  rw [binder,holdsRestrict,dischargeSpec,same]
  rfl
end LogicLineages.PersistentMarking.NumberedWindowLexicalDischargeProof
