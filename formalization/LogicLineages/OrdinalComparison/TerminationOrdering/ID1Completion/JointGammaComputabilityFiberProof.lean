module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityFiberProof
open Source PositiveArithmeticTransforms NumberedLeastCodeRepresentative JointGammaComputability

theorem applicationResultFiber (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain x a z : Nat)
    (h : JointGammaApplication.encodedApplication n arity context domain codomain
      (ContextUniform.objectCode Gamma x) (ContextUniform.objectCode Gamma a) z) :
    ∃ b : Nat, z = ContextUniform.objectCode Gamma b := by
  obtain ⟨Delta,u,v,b,hf,_,hz,_⟩ := h
  simp only [ContextUniform.objectCode,Encodable.encodek,Option.some.injEq,Prod.mk.injEq] at hf
  rcases hf with ⟨he,_⟩
  subst Delta
  exact ⟨b,((JointGammaDomainCodecProof.actualObjectCodec.2.1 z (Gamma,b)).mp hz).symm⟩

theorem actualOriginalComputabilityFibers : JointGammaComputabilityTargets.ActualOriginalComputabilityFibers := by
  intro n arity Gamma P context tau x
  induction tau generalizing x with
  | ground =>
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr (JointGammaTypedProof.actualOriginalContextFibers n arity Gamma context (typeNumber .ground) x) Iff.rfl
  | arrow sigma tau ihs iht =>
    change (_ ∧ ∀ u, JointGammaDomain.sameContext (ContextUniform.objectCode Gamma x) u →
      Computable n arity P context sigma u → ∃ z,
      JointGammaApplication.encodedApplication n arity context (typeNumber sigma) (typeNumber tau)
        (ContextUniform.objectCode Gamma x) u z ∧ Computable n arity P context tau z) ↔ (_ ∧ _)
    rw [JointGammaTypedProof.actualOriginalContextFibers]
    apply and_congr Iff.rfl
    rw [(JointGammaDomainProof.actualQuantifierFibers Gamma x
      (fun u => Computable n arity P context sigma u → ∃ z,
        JointGammaApplication.encodedApplication n arity context (typeNumber sigma) (typeNumber tau)
          (ContextUniform.objectCode Gamma x) u z ∧ Computable n arity P context tau z)).1]
    apply forall_congr'
    intro a
    rw [ihs a]
    apply imp_congr Iff.rfl
    constructor
    · rintro ⟨z,happ,hz⟩
      obtain ⟨b,rfl⟩ := applicationResultFiber n arity Gamma context (typeNumber sigma) (typeNumber tau) x a z happ
      exact ⟨b,(JointGammaApplicationProof.actualOriginalContextFibers n arity Gamma context
        (typeNumber sigma) (typeNumber tau) x a b).mp happ,(iht b).mp hz⟩
    · rintro ⟨b,happ,hb⟩
      exact ⟨ContextUniform.objectCode Gamma b,
        (JointGammaApplicationProof.actualOriginalContextFibers n arity Gamma context
          (typeNumber sigma) (typeNumber tau) x a b).mpr happ,(iht b).mpr hb⟩

theorem actualComputabilityTypedness : JointGammaComputabilityTargets.ActualComputabilityTypedness := by
  intro n arity P context tau x h
  cases tau <;> exact h.1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityFiberProof
