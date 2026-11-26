import LogicLineages.PersistentMarking.ProtectedSpineAdequacyOwnerProof
import LogicLineages.PersistentMarking.ProtectedSpineStrictMarkProof
import LogicLineages.PersistentMarking.DecisionClosureStepProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessBasicProof
open Spine DecisionPorts DecisionRequests FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase
open ProtectedSpineCompletenessTargets ProtectedSpineEnvironment ProtectedSpineInterpreterCore
open MarkedConstructorTargets (CopyExact StatExact)

theorem var (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (σ : Ty) (x : Nat) :
    WeakGoal F M Γ (.free σ x) (.free σ x) := by
  intro h
  let E := domain F
  have he := (HereditaryEncodeDecodeProof.encodeDecode E σ Γ _ h.1
    (MarkedConstructorLiteralProof.literalValid E σ Γ x)).2
  have hb := (he Γ h.1 (DecisionPortsProof.extensionRefl Γ)).2.1 (.free σ x) h.2.2
  exact hb.1.trans ((FiniteEqualityProof.expr _ _).mpr rfl)

theorem headPut {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (bs : Args) (t : Expr)
    (hs : PaperTerm S (.head f bs) f.result) (ht : PaperTerm S t f.result)
    (ih : WeakGoal F M Γ (.marked f f.result bs .nil) t) : WeakGoal F M Γ (.head f bs) t := by
  intro h
  have hbit := ih (DecisionClosureStepProof.step S F _ _ (.put hs ht) h)
  change (funTest S (domain F)
        (MarkedFamilyCoherence.weakenParameter (domain F) (ownerAt S F M Γ f f.result bs .nil) Γ) t ||
      (unfoldedValue S F M Γ (.marked f f.result bs .nil)).weak Γ t) = true
  simp [hbit]

theorem funHead {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f g : Head) (bs ts : Args)
    (hs : PaperTerm S (.head f bs) f.result) (ht : PaperTerm S (.head g ts) g.result)
    (he : Equivalent S f g) (hTy : f.result = g.result)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ih : MatchingGoal F M Γ bs ts) : WeakGoal F M Γ (.head f bs) (.head g ts) := by
  intro h
  let E := domain F
  let p := ownerAt S F M Γ f f.result bs .nil
  have hs' := DecisionSourceMarkProof.sourceMark _ _ _ _ _ _ h.2.1
    (show mark (.head f bs) = some (.marked f f.result bs .nil) from rfl)
  have ht' := SpineMarkingProof.markTyped EmptyContext (.head f bs) f.result (.marked f f.result bs .nil) hs.1 rfl
  have hp := ProtectedSpineAdequacyOwnerProof.valid S F M Γ f f.result bs .nil hm h.1 hs' ht'
  have hb := ProtectedSpineAdequacyOwnerProof.unchangedBase S F M Γ f f.result bs .nil hm h.1 hs' ht'
  have hMatch := ih (DecisionClosureStepProof.step S F _ _ (.funHead hs ht he hTy) h)
  have hMatch' : MarkedConstructorTests.matching E Γ (f.arguments.zip p.2.2.2.1)
      (MarkedConstructorTests.terms ts) = true := by
    change MarkedConstructorTests.matching E Γ (f.arguments.zip (ownerAt S F M Γ f f.result bs .nil).2.2.2.1)
      (MarkedConstructorTests.terms ts) = true
    rw [hb]
    exact (MarkedConstructorOccurrenceProof.matching E Γ _ _).mpr hMatch
  have hFun : funTest S E p (.head g ts) = true := by
    simp only [funTest,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨(MarkedConstructorHeadExactProof.equivalent S f g).mpr he,hTy⟩,hMatch'⟩
  change (funTest S E (MarkedFamilyCoherence.weakenParameter E p Γ) (.head g ts) || _) = true
  rw [show MarkedFamilyCoherence.weakenParameter E p Γ = p from MarkedConstructorParameterProof.weakenIdentity _ _ _ hp]
  simp [hFun]

theorem copy {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f g : Head) (bs es ts : Args)
    (hs : PaperTerm S (.marked f g.result bs es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (hPre : Precedes S f g) (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ih : WholeGoal F M Γ f bs es ts) : WeakGoal F M Γ (.marked f g.result bs es) (.head g ts) := by
  intro h
  let p := ownerAt S F M Γ f g.result bs es
  have hp := ProtectedSpineAdequacyOwnerProof.valid S F M Γ f g.result bs es hm h.1 h.2.1 hs.1
  have hw := ih (DecisionClosureStepProof.step S F _ _ (.copy hs ht hPre) h) g.result
  have hb := (MarkedConstructorHeadExactProof.copy S (domain F) F.data.sourceHeads M p (.head g ts)).mpr
    ⟨g,ts,rfl,rfl,hPre,hw⟩
  rw [ProtectedSpineAdequacyOwnerProof.rootEq S F M Γ f g.result bs es hp]
  simp [MarkedConstructorTests.weakTest,hb,p]

theorem stat {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f g : Head) (bs es ts : Args)
    (hs : PaperTerm S (.marked f g.result bs es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (hEq : Equivalent S f g) (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ih : MultisetGoal F M Γ bs ts) (ih' : WholeGoal F M Γ f bs es ts) :
    WeakGoal F M Γ (.marked f g.result bs es) (.head g ts) := by
  intro h
  let p := ownerAt S F M Γ f g.result bs es
  have hp := ProtectedSpineAdequacyOwnerProof.valid S F M Γ f g.result bs es hm h.1 h.2.1 hs.1
  have hBase := ProtectedSpineAdequacyOwnerProof.unchangedBase S F M Γ f g.result bs es hm h.1 h.2.1 hs.1
  have hList := ih (DecisionClosureStepProof.step S F _ _ (.statBase hs ht hEq) h)
  have hw := ih' (DecisionClosureStepProof.step S F _ _ (.statWhole hs ht hEq) h) g.result
  have hRep : MarkedConstructorTargets.Replaces (domain F) Γ (f.arguments.zip p.2.2.2.1)
      (MarkedConstructorTests.terms ts) := by
    change MarkedConstructorTargets.Replaces (domain F) Γ
      (f.arguments.zip (ownerAt S F M Γ f g.result bs es).2.2.2.1) _
    rw [hBase]
    exact hList
  have hb := (MarkedConstructorHeadExactProof.stat S (domain F) F.data.sourceHeads M p (.head g ts)).mpr
    ⟨g,ts,rfl,rfl,hEq,hRep,hw⟩
  rw [ProtectedSpineAdequacyOwnerProof.rootEq S F M Γ f g.result bs es hp]
  simp [MarkedConstructorTests.weakTest,hb,p]

theorem strict {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (q t r : Expr) (σ : Ty)
    (hq : PaperTerm S q σ) (ht : PaperTerm S t σ) (hr : mark q = some r)
    (ih : WeakGoal F M Γ r t) : StrictGoal F M Γ q t := by
  intro h
  let E := domain F
  have he := (ProtectedSpineAdequacyTypingProof.ends S q t σ hq ht).2.2
  have ho : t ∈ DecisionObservations.observations E.names E.ports Γ E.target q.type := he.symm ▸ h.2.2
  have hb := ProtectedSpineStrictMarkProof.marking S E F.data.sourceHeads M Γ Γ ⟨[],[]⟩ q t
    (sourceCovered S F Γ q h.2.1) (ProtectedSpineConcreteInputProof.emptyValid E Γ h.1)
    (ProtectedSpineStrictInputProof.empty E Γ h.1) h.1 (DecisionPortsProof.extensionRefl Γ) ho
  rw [hr] at hb
  exact hb.trans (ih (DecisionClosureStepProof.step S F _ _ (.strict hq ht hr) h))

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessBasicProof
