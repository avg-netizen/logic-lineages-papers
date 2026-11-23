import LogicLineages.PersistentMarking.NativeTowerExtractorGeneralTargets
import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
import LogicLineages.PersistentMarking.NativeIteratorChecks

namespace LogicLineages.PersistentMarking.NativeTowerExtractorGeneralProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeTowerExtractorGeneralTargets NativeTowerWitnessPrefixTargets

/-- Nearest-first dense slice of the genuine outer h_1,…,h_l,h binders. -/
def binders (top first : Nat) : BoundContext :=
  fun i => if i + first ≤ top then some (ty (i+first)) else none

theorem pushBinder (top first : Nat) (included : first ≤ top) :
    (binders top (first+1)).push (ty first) = binders top first := by
  funext i
  cases i with
  | zero => simp only [BoundContext.push,binders,Nat.zero_add,included,if_true]
  | succ i =>
    have index : i+(first+1) = (i+1)+first := by omega
    simp only [BoundContext.push,binders,index]

theorem pastBinders (top : Nat) : binders top (top+1) = EmptyContext := by
  funext i
  have outside : ¬ (i+(top+1) ≤ top) := by omega
  simp only [binders,outside,if_false,EmptyContext]

/-- The α binder is independent of the type ladder and lies innermost. -/
def innerContext (l : Nat) : BoundContext := (binders (l+1) 1).push indexType

theorem actualInnerLookup (l j : Nat) (positive : 0 < j) (bounded : j ≤ l+1) :
    innerContext l j = some (ty j) := by
  cases j with
  | zero => omega
  | succ j =>
    simp only [innerContext, BoundContext.push, binders, Nat.succ_eq_add_one, bounded, if_true]

private structure OpenNative (S : Signature) (Γ : BoundContext) (q : Expr) (τ : Ty) : Prop where
  typing : Typed Γ q τ
  validity : Valid S q
  ordinary : Ordinary q
  freeClosed : Closed q
  native : Native q

private theorem ofClosed (Γ : BoundContext) (h : ClosedNative S q τ) : OpenNative S Γ q τ :=
  ⟨ClosingProof.weakening q τ h.1.1.1 Γ,h.1.1.2,h.1.2.1,h.1.2.2,h.2⟩

private theorem bound (lookup : Γ i = some τ) : OpenNative S Γ (.bound τ i) τ :=
  ⟨.bound lookup,True.intro,True.intro,fun _ => rfl,fun _ _ => by simp [DecisionInventory.heads]⟩

private theorem application (hf : OpenNative S Γ f (.arrow σ τ)) (hu : OpenNative S Γ u σ) :
    OpenNative S Γ (app σ τ f u) τ where
  typing := .head (.cons hf.typing (.cons hu.typing .nil))
  validity := ⟨⟨0,rfl⟩,hf.validity,hu.validity,True.intro⟩
  ordinary := ⟨hf.ordinary,hu.ordinary,True.intro⟩
  freeClosed := fun n => by simp [app,freeOccurs,freeOccursArgs,hf.freeClosed n,hu.freeClosed n]
  native := fun n k => by
    simp [app,DecisionInventory.heads,DecisionInventory.headsArgs,hf.native n k,hu.native n k]

private theorem abstraction (h : OpenNative S (Γ.push σ) body τ) :
    OpenNative S Γ (.lam σ body) (.arrow σ τ) :=
  ⟨.lam h.typing,h.validity,h.ordinary,h.freeClosed,h.native⟩

private theorem operandOpen (S : Signature) (l k : Nat) (paid : k ≤ l+1) :
    OpenNative S (innerContext l) (lowerOperand k) (ty k) := by
  cases k with
  | zero =>
    exact ofClosed (innerContext l) (NativeOrdinalBasisProof.zeroClosed S)
  | succ j =>
    exact bound (actualInnerLookup l (j+1) (by omega) paid)

private theorem drainOpen (S : Signature) (l k : Nat) (paid : k ≤ l+1) (q : Expr)
    (h : OpenNative S (innerContext l) q (ty k)) :
    OpenNative S (innerContext l) (drain k q) indexType := by
  induction k generalizing q with
  | zero => exact h
  | succ j ih =>
    have lower : j ≤ l+1 := by omega
    exact ih lower (app (ty j) (ty j) q (lowerOperand j))
      (application h (operandOpen S l j lower))

private theorem iteratorOpen (A : SemanticType)
    (i : OpenNative S Γ n indexType) (f : OpenNative S Γ h (functionType A))
    (u : OpenNative S Γ z (actualType A)) : OpenNative S Γ (applied A n h z) (actualType A) :=
  application (application (application (ofClosed Γ (NativeIteratorChecks.exact_ClosedNativeIterator S A)) i) f) u

private theorem innerOpen (S : Signature) (l : Nat) :
    OpenNative S (innerContext l) (inner l) indexType := by
  have arg : OpenNative S (innerContext l) (lowerOperand l) (ty l) :=
    operandOpen S l l (by omega)
  have fn : OpenNative S (innerContext l) (.bound (ty (l+1)) (l+1)) (ty (l+1)) :=
    bound (actualInnerLookup l (l+1) (by omega) (by omega))
  have idx : OpenNative S (innerContext l) (.bound indexType 0) indexType := bound rfl
  exact drainOpen S l l (by omega) _ (iteratorOpen (level l) idx fn arg)

private theorem wrapOpen (S : Signature) (top n : Nat) :
    ∀ (first : Nat) (q : Expr), first+n ≤ top+1 →
      OpenNative S (binders top first) q (ty first) →
      OpenNative S (binders top (first+n)) (bindAscending n first q) (ty (first+n)) := by
  induction n with
  | zero => intro first q hfit h; exact h
  | succ n ih =>
    intro first q hfit h
    have here : first ≤ top := by omega
    have fit : first+1+n ≤ top+1 := by omega
    have step : OpenNative S (binders top (first+1)) (.lam (ty first) q) (ty (first+1)) := by
      have bodyOpen : OpenNative S ((binders top (first+1)).push (ty first)) q (ty first) := by
        rw [pushBinder top first here]
        exact h
      exact abstraction bodyOpen
    have threaded := ih (first+1) (.lam (ty first) q) fit step
    have index : first+1+n = first+(n+1) := by omega
    simpa only [index, bindAscending] using threaded

theorem extractorClosed (S : Signature) (l : Nat) : ClosedNative S (extractor l) (ty (l+2)) := by
  have bodyOpen : OpenNative S (binders (l+1) 1)
      (app endo endo ordinalFix (.lam indexType (inner l))) (ty 1) :=
    application (ofClosed _ (NativeOrdinalExponentialTypingProof.fixClosed S)) (abstraction (innerOpen S l))
  have entire := wrapOpen S (l+1) (l+1) 1 _ (by omega) bodyOpen
  have index : 1+(l+1) = l+2 := by omega
  rw [index, pastBinders (l+1)] at entire
  exact ⟨⟨⟨entire.typing,entire.validity⟩,entire.ordinary,entire.freeClosed⟩,entire.native⟩

theorem exact_GeneralNativeExtractorFamily : ExactGeneralNativeExtractorFamily :=
  ⟨rfl,rfl,extractorClosed⟩

#print axioms pushBinder
#print axioms actualInnerLookup
#print axioms extractorClosed
#print axioms exact_GeneralNativeExtractorFamily
end LogicLineages.PersistentMarking.NativeTowerExtractorGeneralProof
