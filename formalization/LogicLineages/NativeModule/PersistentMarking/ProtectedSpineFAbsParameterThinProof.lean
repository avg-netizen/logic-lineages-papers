module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyOwnerProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineOpeningCodeThinProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineFAbsParameterThinProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets

theorem openedParameter (S : Signature) (F : Inputs S) (M : Code) (Γ : Context)
    (f : Head) (σ τ : Ty) (bs es : Args) (i : Nat)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hσ : σ ∈ F.data.types)
    (h0 : Γ[i]? = some none)
    (hSource : Source F Γ (.marked f (.arrow σ τ) bs es))
    (hTyped : Typed EmptyContext (.marked f (.arrow σ τ) bs es) (.arrow σ τ)) :
    MarkedConstructorTests.fabsParameter (domain F) (ownerAt S F M Γ f (.arrow σ τ) bs es) σ τ i =
      ownerAt S F M (openingContext Γ σ i) f τ bs
        (es.append (.cons (.free σ (portName F.data.names i)) .nil)) := by
  let E := domain F
  let H := F.data.sourceHeads
  let Θ := openingContext Γ σ i
  let x := portName F.data.names i
  let literal := literalCode E Θ σ x
  have hW := MarkedConstructorOpeningProof.openingWellFormed F.data.types F.data.ports Γ σ i hw hσ h0
  have he := MarkedConstructorOpeningProof.openingExtends Γ σ i h0
  have hCov := sourceCovered S F Γ (.marked f (.arrow σ τ) bs es) hSource
  have hBCov := ProtectedSpineCoverageProof.markedBase E H f (.arrow σ τ) bs es hCov
  have hECov := ProtectedSpineCoverageProof.markedExtras E H f (.arrow σ τ) bs es hCov
  cases hTyped with
  | marked hBase hExtras =>
    have hb := ProtectedSpineInterpretationProof.baseLaws S E H M (prefixClosed S F) hm EmptyContext
      bs f.arguments hBase hBCov
    have hx := ProtectedSpineInterpretationProof.extraLaws S E H M (prefixClosed S F) hm EmptyContext es hExtras hECov
    have htypes := ProtectedSpineCoverageProof.argumentTypes E H es hECov
    have hNat' := ProtectedSpineHeadParameterProof.natural E f (.arrow σ τ) (evaluateArgs S E H M bs)
      (evaluateArgs S E H M es) _ hb hx htypes Γ Θ ⟨[],[]⟩
      (ProtectedSpineConcreteInputProof.emptyValid E Γ hw) hW he
    have hNat : MarkedFamilyCoherence.weakenParameter E (ownerAt S F M Γ f (.arrow σ τ) bs es) Θ =
        ownerAt S F M Θ f (.arrow σ τ) bs es := hNat'
    have hEtags : ∀ a, a ∈ concreteTags S F M Θ es → a ∈ MarkedExtras.«universe» E Θ :=
      ProtectedSpineArgumentProof.tags E Θ _ _ ⟨[],[]⟩ hx (ProtectedSpineConcreteInputProof.emptyValid E Θ hW) htypes
    have hLit : ∀ a, a ∈ [(σ,literal)] → a ∈ MarkedExtras.«universe» E Θ := by
      intro a ha
      have he' : a = (σ,literal) := by simpa using ha
      subst a
      exact (MarkedExtrasFoundationProof.universeExact E Θ σ literal).mpr
        ⟨hσ,MarkedConstructorLiteralProof.literalRetained E Θ σ x hW⟩
    have hDown := ProtectedSpineFixedHeadProof.downAppend E Θ (concreteTags S F M Θ es) [(σ,literal)] hW hEtags hLit
    unfold MarkedConstructorTests.fabsParameter
    dsimp only
    change (f,τ,Θ,(MarkedFamilyCoherence.weakenParameter E (ownerAt S F M Γ f (.arrow σ τ) bs es) Θ).2.2.2.1,
      StructuralActions.insertExtras E Θ
        (MarkedFamilyCoherence.weakenParameter E (ownerAt S F M Γ f (.arrow σ τ) bs es) Θ).2.2.2.2
          [(σ,literal)]) = _
    rw [hNat]
    change (f,τ,Θ,(concreteTags S F M Θ bs).map Prod.snd,
      MarkedExtras.down E Θ (MarkedExtras.down E Θ (concreteTags S F M Θ es) ++ [(σ,literal)])) =
      (f,τ,Θ,(concreteTags S F M Θ bs).map Prod.snd,
        MarkedExtras.down E Θ (closedCodes S E H M Θ (es.append (.cons (.free σ x) .nil))))
    rw [hDown,ProtectedSpineConcreteInputProof.append S E H M Θ es (.cons (.free σ x) .nil),
      ProtectedSpineOpeningCodeThinProof.singletonCode S E H M Θ σ x hW]
    rfl

end LogicLineages.PersistentMarking.ProtectedSpineFAbsParameterThinProof
