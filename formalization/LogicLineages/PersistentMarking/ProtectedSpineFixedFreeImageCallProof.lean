import LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallTargets
import LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
import LogicLineages.PersistentMarking.FreeTypingProof
import LogicLineages.PersistentMarking.FreeCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineSubstitutionTargets
open ProtectedSpineFixedApplicationTargets ProtectedSpineFixedFreeImageCallTargets
open ProtectedSpineFreeSubstitutionProof (exact_FreeSubstitution)
open ProtectedSpineFixedApplicationProof (exact_FixedApplication)
open ProtectedSpineConcreteInputProof (argumentTypes fullPrefix emptyValid codeValid)

theorem exact_FixedFreeImageNonemptyCall : FixedFreeImageNonemptyCall := by
  intro S E H M Γ θ q first rest τ a xs hc hm hfix images typed cov covSub callTy argsCov ha hr
  let r := freeSub θ 0 q
  let ds := domainTypes xs
  let values := (closedCodes S E H M Γ xs).map Prod.snd
  have hty : r.type = q.type :=
    FreeCallProof.annotation θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (images.1 σ x)) 0 q
  have rTyped : Typed EmptyContext r r.type := by
    rw [hty]
    exact FreeTypingProof.freeSubTyped EmptyContext θ images.1 q q.type typed
  have rCall : CallTyped EmptyContext r.type xs τ := by
    rw [hty]
    exact callTy
  have tuple : TupleValues E Γ ds values :=
    (codeValid S E H M Γ xs ds hc hm ha.1 ⟨(argumentTypes q.type xs τ callTy).1,argsCov⟩).2
  have prefixOK : (ds,τ) ∈ fullPrefixes q.type := fullPrefix q.type first rest τ callTy
  have agree := exact_FreeSubstitution S E H M θ EmptyContext q q.type 0 hc hm images typed cov
  have same := agree.call Γ ⟨a,[]⟩ ⟨[],[]⟩ 0 0 ds τ values
    ha (emptyValid E Γ ha.1) hr rfl prefixOK tuple
  have identicalCall : call S E H M q Γ a [] ds values τ =
      call S E H M r Γ [] [] ds values τ := by
    exact same
  exact identicalCall.trans
    (exact_FixedApplication S E H M Γ r xs τ hc hm hfix ha.1 rTyped covSub rCall argsCov)

#print axioms exact_FixedFreeImageNonemptyCall
end LogicLineages.PersistentMarking.ProtectedSpineFixedFreeImageCallProof
