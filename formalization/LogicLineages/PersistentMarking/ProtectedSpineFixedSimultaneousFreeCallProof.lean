import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeTupleProof
import LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallProof
import LogicLineages.PersistentMarking.SpineCallTypingProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineSubstitutionTargets
open ProtectedSpineFixedApplicationTargets ProtectedSpineFixedSimultaneousFreeCallTargets
open ProtectedSpineFixedFreeImageCallProof (exact_FixedFreeImageNonemptyCall)
open ProtectedSpineFixedSimultaneousFreeTupleProof

theorem exact_FixedSimultaneousFreeNonemptyCall : FixedSimultaneousFreeNonemptyCall := by
  intro S E H M Γ θ q first rest τ a xs ys hc hm hfix images typed cov covSub callTy ix iy valid related
  have ht := SpineCallTypingProof.callExtras EmptyContext q.type xs τ callTy
  have codes : evaluateArgs S E H M xs Γ a [] = closedCodes S E H M Γ ys :=
    exact_FreeImageTupleCodes S E H M Γ θ a xs hc hm images ht ix valid related
  have doms : domainTypes ys = domainTypes xs := exact_FreeImageTupleDomains θ images.1 xs
  have rCall : CallTyped EmptyContext q.type ys τ :=
    exact_FreeImageTupleCallTyped θ images.1 q.type xs τ callTy
  have result := exact_FixedFreeImageNonemptyCall S E H M Γ θ q (freeSub θ 0 first)
    (freeSubArgs θ 0 rest) τ a hc hm hfix images typed cov covSub rCall iy valid related
  change call S E H M q Γ a [] (domainTypes ys) ((closedCodes S E H M Γ ys).map Prod.snd) τ =
      concreteOutput S E H M Γ τ (apply (freeSub θ 0 q) ys) at result
  rw [doms] at result
  rw [codes]
  exact result

#print axioms exact_FixedSimultaneousFreeNonemptyCall
end LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallProof
