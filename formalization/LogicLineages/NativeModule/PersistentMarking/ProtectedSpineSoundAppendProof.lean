module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundSourceProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundOwnerProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorAppendProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundAppendProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundStageTargets
open ProtectedSpineSoundSourceProof
open MarkedFamilyParameters (Parameter)

theorem insert (F : Inputs S) (Γ : Context) (es args : Args) (old fresh : List MarkedExtras.Tagged)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (he : ExtrasRelated F Γ es old) (ha : ExtrasRelated F Γ args fresh) :
    ExtrasRelated F Γ (es.append args) (StructuralActions.insertExtras (domain F) Γ old fresh) := by
  intro a hm
  obtain ⟨hc,b,hb,hle⟩ := (MarkedExtrasFoundationProof.downExact (domain F) Γ (old++fresh) a).mp hm
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨i,q,hi,hr,hq⟩ := he b hb
    obtain ⟨ht,ha'⟩ := ProtectedSpineSoundOwnerProof.downTag F Γ a b q hw hc hle hq
    exact ⟨i,q,atAppendLeft hi,ht.trans hr,ha'⟩
  · obtain ⟨i,q,hi,hr,hq⟩ := ha b hb
    obtain ⟨j,hj⟩ := atAppendRight es hi
    obtain ⟨ht,ha'⟩ := ProtectedSpineSoundOwnerProof.downTag F Γ a b q hw hc hle hq
    exact ⟨j,q,hj,ht.trans hr,ha'⟩

theorem tupleRelated (F : Inputs S) (Γ : Context) (ds : List Ty) (xs : List Code) (τ : Ty) (args : Args)
    (ht : CallTyped EmptyContext (ArrowPrefix ds τ) args τ)
    (h : ∀ i ρ x a, ds[i]? = some ρ → xs[i]? = some x → At args i a →
      ProtectedSpineSoundRelation.Related F ρ Γ x (some a)) :
    ExtrasRelated F Γ args (ds.zip xs) := by
  rintro ⟨ρ,x⟩ hx
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨hd,hx⟩ := List.getElem?_zip_eq_some.mp hi
  obtain ⟨q,hq,ht⟩ := atCall ht hd
  exact ⟨i,q,hq,ht.symm,h i ρ x q hd hx hq⟩

theorem appended (F : Inputs S) (f : Head) (σ τ : Ty) (Γ : Context)
    (base : List Code) (extras : List MarkedExtras.Tagged) (bs es args : Args)
    (ds : List Ty) (xs : List Code)
    (ho : OwnerRelated F (f,σ,Γ,base,extras) bs es)
    (hv : MarkedFamilyParameters.Valid (domain F) F.data.sourceHeads
      (MarkedConstructorAppendProof.appendParameter (domain F) (f,σ,Γ,base,extras) τ ds xs))
    (hu : Source F Γ (.marked f τ bs (es.append args)))
    (ht : ExtrasTyped EmptyContext args)
    (hr : ExtrasRelated F Γ args (ds.zip xs)) :
    OwnerRelated F (MarkedConstructorAppendProof.appendParameter (domain F) (f,σ,Γ,base,extras) τ ds xs)
      bs (es.append args) := by
  have hTyped : Typed EmptyContext (.marked f τ bs (es.append args)) τ := by
    have hPaper := ho.2.1
    cases hPaper.1 with
    | marked hb he => exact .marked hb (SpineCallTypingProof.appendExtras _ _ _ he ht)
  exact ⟨hv,⟨hTyped,validSource F Γ _ hu⟩,hu,ho.2.2.2.1,
    insert F Γ es args extras (ds.zip xs) ho.1.2.2.1 ho.2.2.2.2 hr⟩

end LogicLineages.PersistentMarking.ProtectedSpineSoundAppendProof
