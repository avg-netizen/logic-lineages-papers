import LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallTargets
import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeTupleProof
import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationProof
import LogicLineages.PersistentMarking.HereditaryEncodingCongruenceProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineFixedMixedFrameCallTargets ProtectedSpineFixedSimultaneousFreeTupleProof
open ProtectedSpineFreeSubstitutionProof (exact_FreeSubstitution)
open ProtectedSpineFixedApplicationProof (exact_FixedApplicationAux)
open ProtectedSpineConcreteInputProof (argumentTypes boundValid codeValid fullPrefix)

theorem exact_FixedMixedFrameCall : FixedMixedFrameCall := by
  intro S E H M Γ θ q xs consumed types τ a ys hc hm hfix images bound typed cov covSub callTy ix iy valid related
  let C := BoundContext.prefix types EmptyContext
  let r := freeSub θ 0 q
  let b := closedCodes S E H M Γ consumed
  have hty : r.type = q.type :=
    FreeCallProof.annotation θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (images.1 σ x)) 0 q
  have imagesHere : FreeMapTyped C θ := by
    intro σ x
    have compatibility : ShiftCompatible 0 0 EmptyContext C := by
      intro i τ hi
      cases hi
    simpa only [SubstitutionProof.shiftZero] using SpineShiftProof.shiftPreserves EmptyContext C
      (θ σ x) σ 0 0 (images.1 σ x) compatibility
  have rt : Typed C r r.type := by
    rw [hty]
    exact FreeTypingProof.freeSubTyped C θ imagesHere q q.type typed
  have rcall : CallTyped EmptyContext r.type ys τ := by
    rw [hty]
    exact exact_FreeImageTupleCallTyped θ images.1 q.type xs τ callTy
  have right : InputValid E Γ ⟨[],b⟩ := boundValid S E H M Γ consumed types hc hm valid.1 bound
  have left : InputValid E Γ ⟨a,b⟩ := ⟨valid.1,valid.2.1,right.2.2⟩
  have hframe : FreeSubstitutionInputs S E H M θ Γ ⟨a,b⟩ ⟨[],b⟩ :=
    ⟨rfl, related.2⟩
  have agree := exact_FreeSubstitution S E H M θ C q q.type 0 hc hm images typed cov
  have transfer : helperWithFree S E H M Γ q xs consumed a τ =
      helperAux S E H M Γ r ys consumed τ := by
    cases xs with
    | nil =>
      have he : q.type = τ := (argumentTypes q.type .nil τ callTy).2.symm
      have same := agree.value Γ ⟨a,b⟩ ⟨[],b⟩ left right hframe
      have enc := HereditaryEncodingCongruenceProof.congruence E q.type Γ _ _ same
      rw [← he]
      simpa [helperWithFree,helperAux,ys,freeSubArgs,r,b,codeAt,ProtectedSpineInterpreterCore.code] using enc
    | cons head rest =>
      let args := Args.cons head rest
      have ht := SpineCallTypingProof.callExtras EmptyContext q.type args τ callTy
      have codes : evaluateArgs S E H M args Γ a [] = closedCodes S E H M Γ ys :=
        exact_FreeImageTupleCodes S E H M Γ θ a args hc hm images ht ix valid related
      have doms : domainTypes ys = domainTypes args := exact_FreeImageTupleDomains θ images.1 args
      have tuple : TupleValues E Γ (domainTypes ys) ((closedCodes S E H M Γ ys).map Prod.snd) :=
        (codeValid S E H M Γ ys (domainTypes ys) hc hm valid.1
          ⟨(argumentTypes r.type ys τ rcall).1,iy⟩).2
      have prefixOK := fullPrefix q.type head rest τ callTy
      have htup : TupleValues E Γ (domainTypes args) ((closedCodes S E H M Γ ys).map Prod.snd) := by
        rw [← doms]
        exact tuple
      have same := agree.call Γ ⟨a,b⟩ ⟨[],b⟩ consumed.length consumed.length
        (domainTypes args) τ ((closedCodes S E H M Γ ys).map Prod.snd)
        left right hframe rfl prefixOK htup
      change nonemptyAt E (evaluate S E H M q) Γ ⟨a,b⟩ consumed.length (domainTypes args) τ
          ((evaluateArgs S E H M args Γ a []).map Prod.snd) =
        nonemptyAt E (evaluate S E H M r) Γ ⟨[],b⟩ consumed.length (domainTypes ys) τ
          ((closedCodes S E H M Γ ys).map Prod.snd)
      rw [codes,doms]
      exact same
  exact transfer.trans (exact_FixedApplicationAux S E H M Γ r ys consumed types τ hc hm hfix
    valid.1 bound rt covSub rcall iy)

#print axioms exact_FixedMixedFrameCall
end LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallProof
