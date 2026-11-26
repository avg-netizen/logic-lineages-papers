module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyOwnerProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureStepProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessWholeProof
open Spine DecisionPorts DecisionRequests FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineFixedApplicationTargets
open MarkedConstructorOperator (step)

theorem nil (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (bs es : Args) :
    WholeGoal F M Γ f bs es .nil := by
  intro h ρ t ht
  cases ht

theorem cons {S : Signature} (F : Inputs S) (M : Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M)
    (Γ : Context) (f : Head) (bs es : Args) (q : Expr) (qs : Args)
    (h : PortComparison.Weak S F.data.types F.data.names Γ (.marked f q.type bs es) q)
    (ih : WeakGoal F M Γ (.marked f q.type bs es) q)
    (ihTail : WholeGoal F M Γ f bs es qs) :
    WholeGoal F M Γ f bs es (.cons q qs) := by
  intro hj ρ t ht
  rcases List.mem_cons.mp ht with he | ht
  · subst t
    have hd := DecisionClosureStepProof.step S F _ _ .wholeHead hj
    have hTyped := (ProtectedSpineAdequacyTypingProof.weak S F.data.types F.data.names Γ _ q h).1.1
    let c := concreteOutput S (domain F) F.data.sourceHeads M Γ q.type (some (.marked f q.type bs es))
    have ho := ProtectedSpineAdequacyOwnerProof.previous S F M Γ f q.type bs es hm hfix hd.1 hd.2.1 hTyped
    have hb := rootBits S F M Γ (.marked f q.type bs es) q hm hd.1 hd.2.1 hTyped hd.2.2 rfl
    exact ⟨c,ho,hb.1.trans (ih hd)⟩
  · exact ihTail (DecisionClosureStepProof.step S F _ _ .wholeTail hj) ρ t ht

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessWholeProof
