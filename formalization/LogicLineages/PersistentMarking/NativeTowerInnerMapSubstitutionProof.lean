import LogicLineages.PersistentMarking.NativeTowerIndexedEntryTargets
import LogicLineages.PersistentMarking.NativeTowerBetaPathProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.NativeIteratorChecks
import LogicLineages.PersistentMarking.NativeOrdinalBasisChecks
import LogicLineages.PersistentMarking.BoundBlockProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeTowerInnerMapSubstitutionProof
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets
open NativeTowerWitnessPrefixTargets NativeTowerExtractorGeneralTargets
open NativeTowerBetaPathTargets NativeTowerBetaPathProof NativeTowerIndexedEntryTargets

def operandValue : Nat → Expr
  | 0 => ordinalZero
  | k+1 => binderArg k

def paidOperand (S : Signature) : (k : Nat) → ClosedNativeTerm S (ty k)
  | 0 => ⟨ordinalZero,(NativeOrdinalBasisChecks.exact_ClosedOrdinalBasis S).1⟩
  | k+1 => actualArg S k

theorem paidOperandLiteral (S : Signature) (k : Nat) :
    (paidOperand S k).val = operandValue k := by
  cases k with
  | zero => rfl
  | succ k => exact actualArgLiteral S k

/-- The exact remaining original lower arguments, after installing the
printed outer extractor arguments. The last argument is literal Z. -/
def filledDrain : Nat → Expr → Expr
  | 0, q => q
  | k+1, q => filledDrain k (app (ty k) (ty k) q (operandValue k))

def filledInner (l : Nat) (j : Expr) : Expr :=
  filledDrain l (applied (level l) j (binderArg l) (operandValue l))

theorem exact_ConsumedOriginalBinderLookup (n : Nat) :
    ∀ (outer : Args) (k : Nat), (consumedArgs n outer).get k =
      if k < n then some (binderArg k) else outer.get (k-n) := by
  induction n with
  | zero =>
    intro outer k
    simp only [consumedArgs,Nat.not_lt_zero,if_false,Nat.sub_zero]
  | succ n ih =>
    intro outer k
    rw [consumedArgs,ih]
    by_cases below : k < n
    · have also : k < n+1 := by omega
      simp only [below,also,if_true]
    · by_cases equal : k = n
      · subst k
        simp only [Nat.lt_irrefl,if_false,Nat.sub_self,Args.get,Nat.lt_succ_self,if_true]
      · have outside : ¬ k < n+1 := by omega
        have offset : k-n = (k-(n+1))+1 := by omega
        simp only [below,outside,if_false,offset,Args.get]

private def slots (l : Nat) (j : Expr) : Args := .cons j (consumedArgs (l+1) .nil)

private theorem substituteIndex (l : Nat) (j : Expr) :
    substitute (slots l j) 0 (.bound indexType 0) = j := by
  simp only [slots,substitute,Nat.lt_irrefl,if_false,Nat.sub_zero,Args.get,SubstitutionProof.shiftZero]

private theorem substitutePaidBound (l : Nat) (j : Expr) (k : Nat) (hlt : k < l+1) :
    substitute (slots l j) 0 (.bound (ty (k+1)) (k+1)) = binderArg k := by
  have lookup : (consumedArgs (l+1) .nil).get k = some (binderArg k) := by
    rw [exact_ConsumedOriginalBinderLookup,if_pos hlt]
  simp only [slots,substitute,Nat.not_lt_zero,if_false,Nat.sub_zero,Args.get,lookup,
    SubstitutionProof.shiftZero]

private theorem substituteOperand (S : Signature) (l : Nat) (j : Expr) (k : Nat) (fit : k ≤ l+1) :
    substitute (slots l j) 0 (lowerOperand k) = operandValue k := by
  cases k with
  | zero =>
    exact ClosedSyntaxProof.closedSubstitute ordinalZero indexType
      (paidOperand S 0).property.1.1.1 (slots l j)
  | succ k => exact substitutePaidBound l j k (by omega)

private theorem substituteDrain (S : Signature) (l : Nat) (j : Expr) (k : Nat) (fit : k ≤ l+1) :
    ∀ q, substitute (slots l j) 0 (drain k q) =
      filledDrain k (substitute (slots l j) 0 q) := by
  induction k with
  | zero => intro q; rfl
  | succ k ih =>
    intro q
    rw [drain,ih (by omega)]
    change filledDrain k (app (ty k) (ty k) (substitute (slots l j) 0 q)
      (substitute (slots l j) 0 (lowerOperand k))) =
        filledDrain k (app (ty k) (ty k) (substitute (slots l j) 0 q) (operandValue k))
    rw [substituteOperand S l j k (by omega)]

theorem exact_OriginalInnerMapClosedSubstitution (S : Signature) (l : Nat) (j : Expr) :
    substitute (.cons j .nil) 0 (substitute (consumedArgs (l+1) .nil) 1 (inner l)) =
      filledInner l j := by
  have appendBlock : substitute (.cons j .nil) 0 (substitute (consumedArgs (l+1) .nil) 1 (inner l)) =
      substitute (slots l j) 0 (inner l) :=
    BoundBlockProof.block (.cons j .nil) (consumedArgs (l+1) .nil) 0 (inner l)
  have fixed : substitute (slots l j) 0 (iterator (level l)) = iterator (level l) :=
    ClosedSyntaxProof.closedSubstitute _ _
      (NativeIteratorChecks.exact_ClosedNativeIterator S (level l)).1.1.1 (slots l j)
  rw [appendBlock]
  unfold inner filledInner
  rw [substituteDrain S l j l (by omega)]
  have first : substitute (slots l j) 0 (.bound indexType 0) = j := substituteIndex l j
  have second := substitutePaidBound l j l (Nat.lt_succ_self l)
  have third := substituteOperand S l j l (Nat.le_succ l)
  change filledDrain l (app (ty l) (ty l)
    (app (ty (l+1)) (ty (l+1))
      (app indexType (.arrow (ty (l+1)) (ty (l+1)))
        (substitute (slots l j) 0 (iterator (level l)))
        (substitute (slots l j) 0 (.bound indexType 0)))
      (substitute (slots l j) 0 (.bound (ty (l+1)) (l+1))))
    (substitute (slots l j) 0 (lowerOperand l))) =
      filledDrain l (applied (level l) j (binderArg l) (operandValue l))
  rw [fixed,first,second,third] <;> rfl

/-- Exact first beta of the printed higher-type inner map at any real native
index. The literal map may be the witness extracted from the original tower. -/
theorem exact_OriginalInnerMapApplicationBeta (S : Signature) (l : Nat)
    (mapping : ClosedNativeTerm S endo) (j : ClosedNativeTerm S indexType)
    (mapValue : mapping.val = innerMap l) :
    ∃ out : ClosedNativeTerm S indexType, out.val = filledInner l j.val ∧
      Reduction S (applyClosed mapping j).val out.val ∧ NativeBelow out (applyClosed mapping j) := by
  let body := substitute (consumedArgs (l+1) .nil) 1 (inner l)
  have literal : mapping.val = .lam indexType body := mapValue
  have typed : ClosedNative S (.lam indexType body) endo := by
    rw [← literal]
    exact mapping.property
  let exposed : ClosedNativeTerm S endo := ⟨.lam indexType body,typed⟩
  have same : mapping = exposed := Subtype.ext literal
  obtain ⟨out,read,step,strict⟩ := NativeClosedBetaChecks.exact_ClosedNativeBeta S
    indexType indexType body typed j
  rw [same]
  change ∃ target : ClosedNativeTerm S indexType, target.val = filledInner l j.val ∧
    Reduction S (@applyClosed S indexType indexType ⟨.lam indexType body,typed⟩ j).val target.val ∧
    NativeBelow target (@applyClosed S indexType indexType ⟨.lam indexType body,typed⟩ j)
  exact ⟨out,read.trans (exact_OriginalInnerMapClosedSubstitution S l j.val),step,strict⟩

#print axioms exact_ConsumedOriginalBinderLookup
#print axioms exact_OriginalInnerMapClosedSubstitution
#print axioms exact_OriginalInnerMapApplicationBeta

end LogicLineages.PersistentMarking.NativeTowerInnerMapSubstitutionProof
