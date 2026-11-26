import LogicLineages.PersistentMarking.ProtectedSpineSoundAppendProof
import LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase
import LogicLineages.PersistentMarking.DecisionSourceCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundTupleProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment (originalHeadCall)
open MarkedConstructorAppendProof (appendParameter)

theorem nonempty {σ τ : Ty} {ds : List Ty} {args : Args}
    (hp : (ds,τ) ∈ fullPrefixes σ) (ht : CallTyped EmptyContext σ args τ) : Spine.Nonempty args := by
  cases ht with
  | nil =>
    have h := (FinitePrefixProof.proper _ _ _ hp).1
    exact False.elim ((Nat.lt_irrefl _) h)
  | cons => trivial

theorem markedCall (f : Head) (σ τ : Ty) (bs es args : Args)
    (hn : Spine.Nonempty args) (ht : CallTyped EmptyContext σ args τ) :
    apply (.marked f σ bs es) args = some (.marked f τ bs (es.append args)) := by
  have hc := SpineCallTypingProof.consumeExact EmptyContext σ args τ ht
  cases args with
  | nil => exact False.elim hn
  | cons a args =>
    simp only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hc]
    rfl

theorem ordinaryCall (f : Head) (τ : Ty) (bs args : Args)
    (hn : Spine.Nonempty args) (ht : CallTyped EmptyContext f.result args τ) :
    apply (.head f bs) args = apply (.marked f f.result bs .nil) args := by
  have hc := SpineCallTypingProof.consumeExact EmptyContext f.result args τ ht
  cases args with
  | nil => exact False.elim hn
  | cons a args =>
    simp only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hc]
    rfl

theorem marked (F : Inputs S) (M : Code) (f : Head) (σ τ : Ty) (Γ : Context)
    (base : List Code) (extras : List MarkedExtras.Tagged)
    (bs es args : Args) (ds : List Ty) (xs : List Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F (f,σ,Γ,base,extras) bs es) (hM : FamilyRelated F M)
    (hp : (ds,τ) ∈ fullPrefixes σ) (hx : TupleValues (domain F) Γ ds xs)
    (ht : CallTyped EmptyContext σ args τ) (hu : Sources F Γ args)
    (hr : ∀ i ρ x a, ds[i]? = some ρ → xs[i]? = some x → At args i a → Related F ρ Γ x (some a)) :
    Related F τ Γ (originalHeadCall (domain F) F.data.sourceHeads M Γ f σ base extras ds xs τ)
      (apply (.marked f σ bs es) args) := by
  let E := domain F
  let p := appendParameter E (f,σ,Γ,base,extras) τ ds xs
  let r := Expr.marked f τ bs (es.append args)
  have hNext := ProtectedSpineAdequacyBase.prefixClosed S F σ ho.1.2.1 ds τ hp
  have hv := MarkedConstructorAppendProof.appendValid E F.data.sourceHeads (f,σ,Γ,base,extras) τ ds xs
    ho.1 hNext.1 hNext.2 hx
  obtain ⟨c,hc,_⟩ := StructuralMarkedActionProof.sound E F.data.sourceHeads M p hm hv
  have hCall := markedCall f σ τ bs es args (nonempty hp ht) ht
  have hR : Source F Γ r := DecisionSourceCallProof.fullCall _ _ _ _ _ _ _ _ _
    (PortTermStateProof.closed S F) ho.2.1.1 ht ho.2.2.1 hu hCall
  have hEq := (FinitePrefixProof.forward σ ds τ hp).2
  have hRelated := ProtectedSpineSoundAppendProof.tupleRelated F Γ ds xs τ args (hEq.symm ▸ ht) hr
  have hOwner := ProtectedSpineSoundAppendProof.appended F f σ τ Γ base extras bs es args ds xs ho hv hR
    (SpineCallTypingProof.callExtras _ _ _ _ ht) hRelated
  have hOut := hM p c bs (es.append args) hOwner hc
  have hTable : originalHeadCall E F.data.sourceHeads M Γ f σ base extras ds xs τ = c := by
    unfold originalHeadCall
    rw [if_pos ⟨MarkedConstructorTupleProof.prefixResidual hp,hx.1⟩]
    change (StructuralActions.markedAction E F.data.sourceHeads M p).getD _ = c
    rw [hc]
    rfl
  change Related F τ Γ (originalHeadCall E F.data.sourceHeads M Γ f σ base extras ds xs τ)
    (apply (.marked f σ bs es) args)
  rw [hCall,hTable]
  exact hOut

end LogicLineages.PersistentMarking.ProtectedSpineSoundTupleProof
