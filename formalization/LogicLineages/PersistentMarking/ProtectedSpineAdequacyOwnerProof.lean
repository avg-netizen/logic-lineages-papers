import LogicLineages.PersistentMarking.ProtectedSpineCompletenessTargets
import LogicLineages.PersistentMarking.ProtectedSpineAdequacyTypingProof

namespace LogicLineages.PersistentMarking.ProtectedSpineAdequacyOwnerProof
open Spine DecisionInventory DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase
open ProtectedSpineCompletenessTargets ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets
open MarkedConstructorOperator (step)

theorem valid (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hq : Source F Γ (.marked f τ bs es)) (ht : Typed EmptyContext (.marked f τ bs es) τ) :
    MarkedFamilyParameters.Valid (domain F) F.data.sourceHeads (ownerAt S F M Γ f τ bs es) := by
  let E := domain F
  let H := F.data.sourceHeads
  have hk := prefixClosed S F
  have hCovered := sourceCovered S F Γ (.marked f τ bs es) hq
  have hτ := hCovered.1 τ (MarkedConstructorSourceTupleProof.rootSupport (.marked f τ bs es))
  have hBase := ProtectedSpineCoverageProof.markedBase E H f τ bs es hCovered
  have hExtra := ProtectedSpineCoverageProof.markedExtras E H f τ bs es hCovered
  cases ht with
  | marked hbs hes =>
    have hb := ProtectedSpineInterpretationProof.baseLaws S E H M hk hm EmptyContext bs f.arguments hbs hBase
    have he := ProtectedSpineInterpretationProof.extraLaws S E H M hk hm EmptyContext es hes hExtra
    exact ProtectedSpineHeadParameterProof.valid E H f τ (evaluateArgs S E H M bs) (evaluateArgs S E H M es)
      _ hb he (hCovered.2 f List.mem_cons_self) hτ (ProtectedSpineCoverageProof.argumentTypes E H es hExtra)
      Γ ⟨[],[]⟩ (ProtectedSpineConcreteInputProof.emptyValid E Γ hw)

theorem unchangedBase (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hq : Source F Γ (.marked f τ bs es)) (ht : Typed EmptyContext (.marked f τ bs es) τ) :
    f.arguments.zip (ownerAt S F M Γ f τ bs es).2.2.2.1 = concreteTags S F M Γ bs := by
  let E := domain F
  let H := F.data.sourceHeads
  have hCovered := sourceCovered S F Γ (.marked f τ bs es) hq
  have hBase := ProtectedSpineCoverageProof.markedBase E H f τ bs es hCovered
  cases ht with
  | marked hbs hes =>
    have hp := (ProtectedSpineConcreteInputProof.codeValid S E H M Γ bs f.arguments
      (prefixClosed S F) hm hw ⟨hbs,hBase⟩).1
    change f.arguments.zip ((closedCodes S E H M Γ bs).map Prod.snd) = _
    rw [← hp,ProtectedSpineArgumentProof.zipProjections]
    rfl

theorem previous (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hq : Source F Γ (.marked f τ bs es)) (ht : Typed EmptyContext (.marked f τ bs es) τ) :
    StructuralActions.markedAction (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es) =
      some (concreteOutput S (domain F) F.data.sourceHeads M Γ τ (some (.marked f τ bs es))) :=
  ProtectedSpineFixedHeadProof.fixedOutput S (domain F) F.data.sourceHeads M _
    (prefixClosed S F) hm hfix (valid S F M Γ f τ bs es hm hw hq ht)

theorem rootEq (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty) (bs es : Args)
    (pValid : MarkedFamilyParameters.Valid (domain F) F.data.sourceHeads (ownerAt S F M Γ f τ bs es)) (t : Expr) :
    (unfoldedValue S F M Γ (.marked f τ bs es)).weak Γ t =
      MarkedConstructorTests.weakTest S (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es) t := by
  change MarkedConstructorTests.weakTest S (domain F) F.data.sourceHeads M
    (MarkedFamilyCoherence.weakenParameter (domain F) (ownerAt S F M Γ f τ bs es) Γ) t = _
  rw [show MarkedFamilyCoherence.weakenParameter (domain F) (ownerAt S F M Γ f τ bs es) Γ =
      ownerAt S F M Γ f τ bs es from MarkedConstructorParameterProof.weakenIdentity _ _ _ pValid]

end LogicLineages.PersistentMarking.ProtectedSpineAdequacyOwnerProof
