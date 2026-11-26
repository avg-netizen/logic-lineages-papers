import LogicLineages.PersistentMarking.ProtectedSpineSoundAppendProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundBitProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundLiteralProof
import LogicLineages.PersistentMarking.MarkedConstructorFAbsExactProof
import LogicLineages.PersistentMarking.MarkedConstructorCanonicalOpeningProof
import LogicLineages.PersistentMarking.PortMarkedStateProof
import LogicLineages.PersistentMarking.MarkedConstructorLookupProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundFAbsProof
open Spine NameBridge DecisionPorts DecisionObservations ObservationLambda FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment (openingContext openingSlot literalCode)

theorem fabs (F : Inputs S) (M : Code) (f : Head) (ρ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es : Args) (t : Expr)
    (ho : OwnerRelated F (f,ρ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (hObs : t ∈ observations F.data.names F.data.ports Γ F.target ρ)
    (h : MarkedConstructorTargets.FAbsWitness (domain F) F.data.sourceHeads M (f,ρ,Γ,cs,xs) t) :
    Weak S (.marked f ρ bs es) t := by
  obtain ⟨σ,τ,body,i,c,hType,rfl,hi,hc,hBit⟩ := h
  change ρ = .arrow σ τ at hType
  subst ρ
  let E := domain F
  let x := portName F.data.names i
  let Θ := openingContext Γ σ i
  let v := literalCode E Θ σ x
  let w := MarkedFamilyCoherence.weakenParameter E (f,.arrow σ τ,Γ,cs,xs) Θ
  let p := MarkedConstructorTests.fabsParameter E (f,.arrow σ τ,Γ,cs,xs) σ τ i
  let e := Args.cons (.free σ x) .nil
  have hTarget := ProtectedSpineSoundBitProof.observedPaper F Γ (.arrow σ τ) (.lam σ body) hObs
  have hAnn := SpineShiftProof.annotationExact _ _ _ hTarget.1
  have hw := ho.1.2.2.1
  obtain ⟨j,hj,hσ,hΘ,he,hChild⟩ := PortLambdaStateProof.descent S F Γ σ body hw (hAnn.symm ▸ hObs)
  have hActual := MarkedConstructorCanonicalOpeningProof.slotEq Γ j hj
  change openingSlot Γ = some i at hi
  have hji : j=i := Option.some.inj (hActual.symm.trans hi)
  subst j
  rw [←MarkedConstructorCanonicalOpeningProof.openingEqFill Γ σ i] at hΘ he hChild
  have h0 := MarkedConstructorOpeningProof.slotUnused Γ i hi
  have hSlot : Θ[i]? = some (some σ) := by simp [Θ,MarkedConstructorOpeningProof.openingAt,h0]
  have hOpened := PortMarkedStateProof.appendPort S F Γ Θ f σ τ bs es i hΘ he hSlot ho.2.2.1
  have hw' := ProtectedSpineSoundOwnerProof.weaken F (f,.arrow σ τ,Γ,cs,xs) Θ bs es ho hΘ he
  have hp : MarkedFamilyParameters.Valid E F.data.sourceHeads p :=
    (MarkedConstructorLookupProof.actionValid E F.data.sourceHeads M p c hc).1
  have hFresh : ExtrasRelated F Θ e ([σ].zip [v]) := by
    intro a ha
    have hEq : a = (σ,v) := by simpa using ha
    subst a
    exact ⟨0,.free σ x,.here,rfl,ProtectedSpineSoundLiteralProof.literalRelated F Θ σ x hΘ⟩
  have hOwner : OwnerRelated F p bs (es.append e) :=
    ProtectedSpineSoundAppendProof.appended F f (.arrow σ τ) τ Θ w.2.2.2.1 w.2.2.2.2
      bs es e [σ] [v] hw' hp hOpened (.cons .free .nil) hFresh
  have hR := hM p c bs (es.append e) hOwner hc
  have hOpenPaper := ElementarySupportProof.openingPaper S σ τ x body hTarget
  have hOpenType := SpineShiftProof.annotationExact _ _ _ hOpenPaper.1
  have hW := (ProtectedSpineSoundBitProof.bits F Θ τ _ _ c hΘ (hOpenType ▸ hChild) hR).1 hBit
  have hObsSource := PortStateProof.observedUniverse S F Γ (.lam σ body) hw (hAnn.symm ▸ hObs)
  have hBody := DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hObsSource
  exact .fabs ho.2.1 hTarget (PortStateProof.unusedAbsent _ _ _ _ _ _ _ ho.2.2.1 h0)
    (PortStateProof.unusedAbsent _ _ _ _ _ _ _ hBody h0) hW

end LogicLineages.PersistentMarking.ProtectedSpineSoundFAbsProof
