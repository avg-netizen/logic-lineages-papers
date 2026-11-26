module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineListTransportProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyTypingProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureStepProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessListProof
open Spine DecisionPorts DecisionRequests FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase
open ProtectedSpineCompletenessTargets ProtectedSpineListTransportProof

theorem matchingNil (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) :
    MatchingGoal F M Γ .nil .nil := fun _ => .nil

theorem matchingCons {S : Signature} (F : Inputs S) (M : Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (Γ : Context) (x y : Expr) (xs ys rest : Args) (hremove : Remove ys y rest)
    (hxy : PortComparison.Weak S F.data.types F.data.names Γ x y)
    (ih : WeakGoal F M Γ x y) (ihTail : MatchingGoal F M Γ xs rest) :
    MatchingGoal F M Γ (.cons x xs) ys := by
  intro hj
  have hhead := DecisionClosureStepProof.step S F _ _ (.matchingHead hremove) hj
  have htail := DecisionClosureStepProof.step S F _ _ (.matchingTail hremove) hj
  have hty := ProtectedSpineAdequacyTypingProof.weak S F.data.types F.data.names Γ x y hxy
  have hbit := ProtectedSpineAdequacyTypingProof.taggedBit S F M Γ x y hm hhead.1
    hhead.2.1 hhead.2.2 hty false (ih hhead)
  exact .cons (removeTerms hremove) hbit (ihTail htail)

theorem coverageNil (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (owners : Args) :
    CoverageGoal F M Γ owners .nil := by
  intro h t ht
  cases ht

theorem coverageCons {S : Signature} (F : Inputs S) (M : Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (Γ : Context) (q t : Expr) (i : Nat) (owners ts : Args) (hAt : At owners i q)
    (hqt : PortComparison.Strict S F.data.types F.data.names Γ q t)
    (ih : StrictGoal F M Γ q t) (ihTail : CoverageGoal F M Γ owners ts) :
    CoverageGoal F M Γ owners (.cons t ts) := by
  intro hj u hu
  rcases List.mem_cons.mp hu with he | hu
  · subst u
    have hhead := DecisionClosureStepProof.step S F _ _ (.coverageHead hAt) hj
    have hty := ProtectedSpineAdequacyTypingProof.strict S F.data.types F.data.names Γ q t hqt
    have hbit := ProtectedSpineAdequacyTypingProof.taggedBit S F M Γ q t hm hhead.1
      hhead.2.1 hhead.2.2 hty true (ih hhead)
    exact ⟨_,atTag S F M Γ hAt,hbit⟩
  · exact ihTail (DecisionClosureStepProof.step S F _ _ (.coverageTail hAt) hj) u hu

theorem multiset {S : Signature} (F : Inputs S) (M : Code) (Γ : Context)
    (qs ts kept removed matched added : Args) (hs : Split qs kept removed) (ht : Split ts matched added)
    (hn : Spine.Nonempty removed) (ihMatch : MatchingGoal F M Γ kept matched) (ihCover : CoverageGoal F M Γ removed added) :
    MultisetGoal F M Γ qs ts := by
  intro hj
  have hm := DecisionClosureStepProof.step S F _ _ (.multisetMatch hs ht hn) hj
  have hc := DecisionClosureStepProof.step S F _ _ (.multisetCover hs ht hn) hj
  exact ⟨_,_,_,_,splitTags S F M Γ hs,splitTerms ht,nonemptyTags S F M Γ removed hn,ihMatch hm,ihCover hc⟩

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessListProof
