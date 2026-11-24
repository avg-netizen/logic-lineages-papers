import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallTargets
import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeCallProof
import LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
import LogicLineages.PersistentMarking.HereditaryEncodingCongruenceProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineFixedApplicationTargets
open ProtectedSpineFixedSimultaneousFreeAllCallTargets
open ProtectedSpineFixedSimultaneousFreeCallProof (exact_FixedSimultaneousFreeNonemptyCall)
open ProtectedSpineFreeSubstitutionProof (exact_FreeSubstitution)
open ProtectedSpineConcreteInputProof (argumentTypes emptyValid)

theorem exact_FixedSimultaneousFreeAllCall : FixedSimultaneousFreeAllCall := by
  intro S E H M Γ θ q xs τ a ys hc hm hfix images typed cov covSub callTy ix iy valid related
  cases xs with
  | nil =>
    have he : q.type = τ := (argumentTypes q.type .nil τ callTy).2.symm
    have agree := exact_FreeSubstitution S E H M θ EmptyContext q q.type 0 hc hm images typed cov
    have same := agree.value Γ ⟨a,[]⟩ ⟨[],[]⟩ valid (emptyValid E Γ valid.1) related
    have encoded := HereditaryEncodingCongruenceProof.congruence E q.type Γ _ _ same
    rw [← he]
    simpa [ys,call,domainTypes,MarkedConstructorTests.terms,evaluateArgs,freeSubArgs,apply,
      concreteOutput,interpret,codeAt,valueAt,ProtectedSpineInterpreterCore.code] using encoded
  | cons first rest =>
    exact exact_FixedSimultaneousFreeNonemptyCall S E H M Γ θ q first rest τ a
      hc hm hfix images typed cov covSub callTy ix iy valid related

#print axioms exact_FixedSimultaneousFreeAllCall
end LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallProof
