import LogicLineages.PersistentMarking.NativeStructuralRealizationSyntax
import LogicLineages.PersistentMarking.ClosingProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof
import LogicLineages.PersistentMarking.SpineSubstitutionProof
import LogicLineages.PersistentMarking.SubstitutionProof

namespace LogicLineages.PersistentMarking.NativeStructuralRealizationClosingProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeStructuralRealizationSyntax
open DecisionInventory

theorem indexedLookup (i : Var Γ A) : rawContext Γ i.index = some (actualType A) := by
  induction i with
  | here => rfl
  | there i ih => exact ih

theorem literalTyping : ExactLiteralStructuralTyping := by
  intro S C lit Γ A t
  induction t with
  | var i => exact .bound (indexedLookup i)
  | app A D f u hf hu => exact .head (.cons hf (.cons hu .nil))
  | lam A body ih => exact .lam ih
  | literal k => exact ClosingProof.weakening _ _ (lit _ k).property.1.1.1 _

private theorem contextPrefix (Γ : List SemanticType) :
    rawContext Γ = BoundContext.«prefix» (Γ.map actualType) EmptyContext := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp only [rawContext, List.map_cons, BoundContext.«prefix», ih]

private theorem valuesTyped (ρ : ClosedEnv S Γ) :
    BaseTyped EmptyContext ρ.args (Γ.map actualType) := by
  induction ρ with
  | nil => exact .nil
  | cons q ρ ih => exact .cons q.property.1.1.1 ih

private theorem valuesRead (ρ : ClosedEnv S Γ) (i : Nat) (q : Expr)
    (h : ρ.args.get i = some q) : ∃ A, ClosedNative S q (actualType A) := by
  induction ρ generalizing i with
  | nil => cases i <;> simp [ClosedEnv.args, Args.get] at h
  | @cons Γ A v ρ ih =>
    cases i with
    | zero =>
      have eq : v.val = q := Option.some.inj h
      subst q
      exact ⟨A, v.property⟩
    | succ i => exact ih i h

private theorem unchanged (v : ClosedNativeTerm S τ) (values : Args) (d : Nat) :
    substitute values d v.val = v.val := by
  have empty : ClosedSyntaxProof.Bounded EmptyContext d := by intro i A h; cases h
  exact (ClosedSyntaxProof.term EmptyContext d empty v.val τ v.property.1.1.1 0 values).2

private structure Shape (S : Signature) (q : Expr) : Prop where
  valid : Valid S q
  ordinary : Ordinary q
  closed : Closed q
  native : Native q

private theorem closedShape (h : ClosedNative S q τ) : Shape S q :=
  ⟨h.1.1.2,h.1.2.1,h.1.2.2,h.2⟩

private theorem boundShape (S : Signature) (τ : Ty) (i : Nat) : Shape S (.bound τ i) := by
  refine ⟨True.intro,True.intro,fun _ => rfl,?_⟩
  intro name arity
  simp only [DecisionInventory.heads,List.not_mem_nil]
  exact fun impossible => impossible

private theorem sourceAppShape (σ τ : Ty) (q u : Expr)
    (hq : Shape S q) (hu : Shape S u) : Shape S (app σ τ q u) := by
  refine ⟨⟨⟨0,rfl⟩,hq.valid,hu.valid,True.intro⟩,⟨hq.ordinary,hu.ordinary,True.intro⟩,?_,?_⟩
  · intro n
    simp [app,freeOccurs,freeOccursArgs,hq.closed n,hu.closed n]
  · intro name arity
    simp [app,DecisionInventory.heads,DecisionInventory.headsArgs,hq.native name arity,hu.native name arity]

private theorem scopedShape (lit : Literals S C) (t : Fragment C Γ A) :
    ∀ {Δ}, (ρ : ClosedEnv S Δ) → ∀ d, Shape S (substitute ρ.args d (t.raw lit)) := by
  induction t with
  | @var Γ A i =>
    intro Δ ρ d
    by_cases lower : i.index < d
    · simpa only [Fragment.raw,substitute,if_pos lower] using boundShape S (actualType A) i.index
    · cases looked : ρ.args.get (i.index - d) with
      | none =>
        simpa only [Fragment.raw,substitute,if_neg lower,looked] using
          boundShape S (actualType A) (i.index - ρ.args.length)
      | some v =>
        obtain ⟨B,typed⟩ := valuesRead ρ _ v looked
        have still := ClosedSyntaxProof.closedShift v (actualType B) typed.1.1.1 d
        simpa only [Fragment.raw,substitute,if_neg lower,looked,still] using closedShape typed
  | app A D f u hf hu =>
    intro Δ ρ d
    exact sourceAppShape (actualType A) (actualType D) _ _ (hf ρ d) (hu ρ d)
  | lam A body ih =>
    intro Δ ρ d
    have h := ih ρ (d+1)
    exact ⟨h.valid,h.ordinary,h.closed,h.native⟩
  | literal k =>
    intro Δ ρ d
    rw [Fragment.raw, unchanged (lit _ k)]
    exact closedShape (lit _ k).property

/-- Type and inhabit the exact original simultaneous substitution. -/
def instantiate (lit : Literals S C) (t : Fragment C Γ A) (ρ : ClosedEnv S Γ) :
    ClosedNativeTerm S (actualType A) := by
  have typed := literalTyping S C lit Γ A t
  rw [contextPrefix] at typed
  have closedTyped := SpineSubstitutionProof.parallelPreserves EmptyContext (Γ.map actualType)
    ρ.args (t.raw lit) (actualType A) (valuesTyped ρ) typed
  have shape := scopedShape lit t ρ 0
  exact ⟨substitute ρ.args 0 (t.raw lit),⟨⟨⟨closedTyped,shape.valid⟩,shape.ordinary,shape.closed⟩,shape.native⟩⟩

theorem literalInstantiation (lit : Literals S C) (t : Fragment C Γ A) (ρ : ClosedEnv S Γ) :
    (instantiate lit t ρ).val = substitute ρ.args 0 (t.raw lit) := rfl

private theorem lookupArgs (ρ : ClosedEnv S Γ) (i : Var Γ A) :
    ρ.args.get i.index = some (ρ.lookup i).val := by
  induction i with
  | here => cases ρ; rfl
  | there i ih =>
    cases ρ with
    | cons q rest => exact ih rest

theorem instantiatedVar (lit : Literals S C) (ρ : ClosedEnv S Γ) (i : Var Γ A) :
    instantiate lit (.var i) ρ = ρ.lookup i := by
  apply Subtype.ext
  rw [literalInstantiation]
  simp only [Fragment.raw,substitute,Nat.not_lt_zero,if_false,Nat.sub_zero,lookupArgs,
    SubstitutionProof.shiftZero]

theorem instantiatedApp (lit : Literals S C) (ρ : ClosedEnv S Γ)
    (f : Fragment C Γ (.arrow A D)) (u : Fragment C Γ A) :
    instantiate lit (.app A D f u) ρ = applyClosed (instantiate lit f ρ) (instantiate lit u ρ) :=
  Subtype.ext rfl

theorem instantiatedConstant (lit : Literals S C) (ρ : ClosedEnv S Γ) (k : C A) :
    instantiate lit (.literal k) ρ = lit A k := by
  apply Subtype.ext
  rw [literalInstantiation]
  exact unchanged (lit A k) ρ.args 0

end LogicLineages.PersistentMarking.NativeStructuralRealizationClosingProof
