module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineConcreteInputProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorEndomapProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryCodeReconstructionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedHeadProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineFixedApplicationTargets ProtectedSpineConcreteInputProof
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)
open MarkedFamilyParameters (Parameter)

theorem downAppend (E : Environment) (Γ : Context) (xs ys : List MarkedExtras.Tagged)
    (hw : WellFormed E.types E.ports Γ)
    (hx : ∀ a, a ∈ xs → a ∈ MarkedExtras.«universe» E Γ)
    (hy : ∀ a, a ∈ ys → a ∈ MarkedExtras.«universe» E Γ) :
    MarkedExtras.down E Γ (MarkedExtras.down E Γ xs ++ ys) = MarkedExtras.down E Γ (xs ++ ys) := by
  apply MarkedExtrasDownProof.canonicalExt E Γ _ _
    (MarkedExtrasDownProof.canonicalFilter E Γ _) (MarkedExtrasDownProof.canonicalFilter E Γ _)
  intro a hau
  have hOrd := MarkedExtrasFoundationProof.order E Γ hw
  constructor
  · intro ha
    obtain ⟨_,b,hb,hab⟩ := (MarkedExtrasFoundationProof.downExact E Γ _ a).mp ha
    apply (MarkedExtrasFoundationProof.downExact E Γ _ a).mpr
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨hbu,c,hc,hbc⟩ := (MarkedExtrasFoundationProof.downExact E Γ _ b).mp hb
      exact ⟨hau,c,List.mem_append_left _ hc,hOrd.2.1 a b c hau hbu (hx c hc) hab hbc⟩
    · exact ⟨hau,b,List.mem_append_right _ hb,hab⟩
  · intro ha
    obtain ⟨_,b,hb,hab⟩ := (MarkedExtrasFoundationProof.downExact E Γ _ a).mp ha
    apply (MarkedExtrasFoundationProof.downExact E Γ _ a).mpr
    rcases List.mem_append.mp hb with hb | hb
    · have hbu := hx b hb
      have hbd := (MarkedExtrasFoundationProof.downExact E Γ xs b).mpr ⟨hbu,b,hb,hOrd.1 b hbu⟩
      exact ⟨hau,b,List.mem_append_left _ hbd,hab⟩
    · exact ⟨hau,b,List.mem_append_right _ hb,hab⟩

theorem fixedOutput (S : Signature) (E : Environment) (H : List Head) (M : Code) (p : Parameter)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hfix : step S E H M = M)
    (hp : MarkedFamilyParameters.Valid E H p) :
    StructuralActions.markedAction E H M p =
      some (HereditaryDomainSemantics.encode E p.2.1 p.2.2.1 (MarkedConstructorValue.build S E H M p)) := by
  have h := (MarkedConstructorEndomapProof.endomap S E H hc M hm).2.2 p hp
  rw [hfix] at h
  obtain ⟨c,hc',hcm⟩ := StructuralMarkedActionProof.sound E H M p hm hp
  rw [StructuralMarkedActionProof.decoded E H M p c hc'] at h
  have he := HereditaryEncodingCongruenceProof.congruence E p.2.1 p.2.2.1 _ _ h
  rw [HereditaryCodeReconstructionProof.reconstruct E p.2.1 p.2.2.1 c hcm] at he
  rw [hc',he]

theorem afterAppend (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (f : Head) (σ τ : Ty) (base extras args : Args)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hfix : step S E H M = M)
    (hw : WellFormed E.types E.ports Γ) (hf : f ∈ H) (hτ : τ ∈ E.types)
    (hb : BaseTyped EmptyContext base f.arguments) (hbCov : ArgsCovered E H base)
    (he : ExtrasTyped EmptyContext extras) (heCov : ArgsCovered E H extras)
    (ha : CallTyped EmptyContext σ args τ) (haCov : ArgsCovered E H args) :
    originalHeadCall E H M Γ f σ ((closedCodes S E H M Γ base).map Prod.snd)
      (MarkedExtras.down E Γ (closedCodes S E H M Γ extras)) (domainTypes args)
      ((closedCodes S E H M Γ args).map Prod.snd) τ =
    concreteOutput S E H M Γ τ (some (.marked f τ base (extras.append args))) := by
  let bs := closedCodes S E H M Γ base
  let es := closedCodes S E H M Γ extras
  let vs := closedCodes S E H M Γ args
  have hArgs := argumentTypes σ args τ ha
  have hbl := codeValid S E H M Γ base f.arguments hc hm hw ⟨hb,hbCov⟩
  have hAl := codeValid S E H M Γ args (domainTypes args) hc hm hw ⟨hArgs.1,haCov⟩
  have hEs := ProtectedSpineInterpretationProof.extraLaws S E H M hc hm EmptyContext extras he heCov
  have hEtags : ∀ a, a ∈ es → a ∈ MarkedExtras.«universe» E Γ :=
    ProtectedSpineArgumentProof.tags E Γ _ _ ⟨[],[]⟩ hEs (emptyValid E Γ hw)
      (ProtectedSpineCoverageProof.argumentTypes E H extras heCov)
  have hArgsLaw := ProtectedSpineInterpretationProof.baseLaws S E H M hc hm EmptyContext args
    (domainTypes args) hArgs.1 haCov
  have hVtags : ∀ a, a ∈ vs → a ∈ MarkedExtras.«universe» E Γ :=
    ProtectedSpineArgumentProof.tags E Γ _ _ ⟨[],[]⟩ hArgsLaw (emptyValid E Γ hw)
      (ProtectedSpineCoverageProof.argumentTypes E H args haCov)
  have hzip : (domainTypes args).zip (vs.map Prod.snd) = vs := by
    rw [← hAl.1,ProtectedSpineArgumentProof.zipProjections]
  let p : Parameter := (f,τ,Γ,bs.map Prod.snd,MarkedExtras.down E Γ (es ++ vs))
  have hp : MarkedFamilyParameters.Valid E H p :=
    ⟨hf,hτ,hw,hbl.2,MarkedExtrasDownProof.downExtra E Γ _ hw (fun a h =>
      (List.mem_append.mp h).elim (hEtags a) (hVtags a))⟩
  have hLookup := fixedOutput S E H M p hc hm hfix hp
  have hAdd := downAppend E Γ es vs hw hEtags hVtags
  change originalHeadCall E H M Γ f σ (bs.map Prod.snd) (MarkedExtras.down E Γ es)
    (domainTypes args) (vs.map Prod.snd) τ =
      HereditaryDomainSemantics.encode E τ Γ (MarkedConstructorValue.build S E H M
        (f,τ,Γ,bs.map Prod.snd,MarkedExtras.down E Γ (closedCodes S E H M Γ (extras.append args))))
  rw [append S E H M Γ extras args]
  unfold originalHeadCall
  rw [if_pos ⟨residual σ args τ ha,hAl.2.1⟩,hzip]
  change (StructuralActions.markedAction E H M
    (f,τ,Γ,bs.map Prod.snd,MarkedExtras.down E Γ (MarkedExtras.down E Γ es ++ vs))).getD _ = _
  rw [hAdd]
  change (StructuralActions.markedAction E H M p).getD _ = _
  rw [hLookup]
  rfl

end LogicLineages.PersistentMarking.ProtectedSpineFixedHeadProof
