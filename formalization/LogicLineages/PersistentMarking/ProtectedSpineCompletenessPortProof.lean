import LogicLineages.PersistentMarking.ProtectedSpineCompletenessListProof
import LogicLineages.PersistentMarking.ProtectedSpineCompletenessWholeProof
import LogicLineages.PersistentMarking.ProtectedSpineCompletenessBasicProof
import LogicLineages.PersistentMarking.ProtectedSpineCompletenessAbsProof
import LogicLineages.PersistentMarking.ProtectedSpineCompletenessFAbsProof
import LogicLineages.PersistentMarking.ProtectedSpineCompletenessSelectProof

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessPortProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineCompletenessTargets
open MarkedConstructorOperator (step)

theorem weak (S : Signature) (F : Inputs S) (M : Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M) (Γ : Context) (q t : Expr)
    (h : PortComparison.Weak S F.data.types F.data.names Γ q t) : WeakGoal F M Γ q t := by
  refine PortComparison.Weak.rec
    (motive_1 := fun Γ q t _ => WeakGoal F M Γ q t)
    (motive_2 := fun Γ q t _ => StrictGoal F M Γ q t)
    (motive_3 := fun Γ qs ts _ => MatchingGoal F M Γ qs ts)
    (motive_4 := fun Γ qs ts _ => MultisetGoal F M Γ qs ts)
    (motive_5 := fun Γ qs ts _ => CoverageGoal F M Γ qs ts)
    (motive_6 := fun Γ f bs es ts _ => WholeGoal F M Γ f bs es ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros
    exact ProtectedSpineCompletenessBasicProof.var S F M _ _ _
  · intros
    rename_i hs ht hK hi hx hy child ih
    exact ProtectedSpineCompletenessAbsProof.abs F M _ _ _ _ _ _ hs ht hm hi ih
  · intros
    rename_i hs ht he hty child ih
    exact ProtectedSpineCompletenessBasicProof.funHead F M _ _ _ _ _ hs ht he hty hm ih
  · intros
    rename_i hs ht child ih
    exact ProtectedSpineCompletenessBasicProof.headPut F M _ _ _ _ hs ht ih
  · intros
    rename_i hs ht hat hty happ child ih
    exact ProtectedSpineCompletenessSelectProof.select F M _ _ _ _ _ _ _ _ _ _ hm hfix hs ht hat hty happ child ih
  · intros
    rename_i hs ht hK hi hx hy child ih
    exact ProtectedSpineCompletenessFAbsProof.fabs F M _ _ _ _ _ _ _ _ hs ht hK hm hfix hi child ih
  · intros
    rename_i hs ht hp child ih
    exact ProtectedSpineCompletenessBasicProof.copy F M _ _ _ _ _ _ hs ht hp hm ih
  · intros
    rename_i hs ht he hmult hwhole ihm ihw
    exact ProtectedSpineCompletenessBasicProof.stat F M _ _ _ _ _ _ hs ht he hm ihm ihw
  · intros
    rename_i hs ht hmark child ih
    exact ProtectedSpineCompletenessBasicProof.strict F M _ _ _ _ _ hs ht hmark ih
  · intros
    exact ProtectedSpineCompletenessListProof.matchingNil S F M _
  · intros
    rename_i hr hweak hm' ihw ihm
    exact ProtectedSpineCompletenessListProof.matchingCons F M hm _ _ _ _ _ _ hr hweak ihw ihm
  · intros
    rename_i hs ht hn hmatch hcover ihm ihc
    exact ProtectedSpineCompletenessListProof.multiset F M _ _ _ _ _ _ _ hs ht hn ihm ihc
  · intros
    exact ProtectedSpineCompletenessListProof.coverageNil S F M _ _
  · intros
    rename_i hat hs hc ihs ihc
    exact ProtectedSpineCompletenessListProof.coverageCons F M hm _ _ _ _ _ _ hat hs ihs ihc
  · intros
    exact ProtectedSpineCompletenessWholeProof.nil S F M _ _ _ _
  · intros
    rename_i hw hs ihw ihs
    exact ProtectedSpineCompletenessWholeProof.cons F M hm hfix _ _ _ _ _ _ hw ihw ihs

theorem strict (S : Signature) (F : Inputs S) (M : Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M) (Γ : Context) (q t : Expr)
    (h : PortComparison.Strict S F.data.types F.data.names Γ q t) : StrictGoal F M Γ q t := by
  cases h with
  | intro hq ht hmark hw =>
    exact ProtectedSpineCompletenessBasicProof.strict F M _ _ _ _ _ hq ht hmark
      (weak S F M hm hfix _ _ _ hw)

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessPortProof
