module
public import LogicLineages.PermittedControl.StandardCombinatorSignedProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardCombinatorCoordinates.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open SelectedHardness
open SelectedHardnessUnusedProof (unusedVector freePart shape1)
open SelectedHardnessCombinatorSyntaxProof (unusedHead)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open Source.FunctionalDetector (pad)
def padVector (p : Policy) {Γ} (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) : OrdinalVector Γ 1 :=
  application (σ:=.ground) (τ:=unary) p (unusedVector p av) qv

theorem pad_assignment (p : Policy) {Γ} (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0)
    (ha : assignment p a=some av) (hq : assignment p q=some qv) :
    assignment p (pad a q)=some (padVector p av qv) :=
  SelectedHardnessCombinatorSyntaxProof.app_assignment p _ _ _ _
    (SelectedHardnessUnusedProof.unused_assignment p a av ha) hq

theorem pad_head_expression (p : Policy) {Γ} (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) :
    padVector p av qv 1=unusedHead (av 1) := by
  change ordinalBoxPositive 0 (@ordinalVectorAt Γ 1 (unusedVector p av))
    (@ordinalVectorAt Γ 0 qv) 1=_
  rw [ordinalBoxPositive]
  simp only [show ¬(1≤0) by omega,dite_false,ordinalVectorAt]
  change .add (AdmissibleSum.expand (p.shape .positiveAbstraction 1)
    (fun i : Fin 2 => freePart av i (1 : Fin 2))) (av 1) = unusedHead (av 1)
  rw [shape1]
  rfl

theorem pad_head (ctrl : Nat → Nat) (p : Policy) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) :
    ParametricSourceSuccessor.denoteWith ctrl ν (padVector p av qv 1)=
      SelectedHardness.paddedHead (ParametricSourceSuccessor.denoteWith ctrl ν (av 1)) := by
  rw [pad_head_expression]
  rfl

theorem pad_scalar (ctrl : Nat → Nat) (p : Policy) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) (a0 q0 : Nat)
    (ha : ParametricSourceSuccessor.denoteWith ctrl ν (av 0)=(a0 : Ordinal))
    (hq : ParametricSourceSuccessor.denoteWith ctrl ν (qv 0)=(q0 : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (padVector p av qv 0)=
      (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (SelectedHardness.paddedHead
          (ParametricSourceSuccessor.denoteWith ctrl ν (av 1))))
        ((5*a0+4+q0 : Nat) : Ordinal)) : Ordinal) := by
  have hh := pad_head_expression p av qv
  have hs := SelectedHardnessScalarSyntaxProof.unused_scalar ctrl p ν av a0 ha
  have he : padVector p av qv 0=.collapse (unusedHead (av 1))
      (.add (unusedVector p av 0) (qv 0)) := by
    change Term.collapse (padVector p av qv 1) (.add (unusedVector p av 0) (qv 0))=_
    rw [hh]
  rw [he]
  simp only [ParametricSourceSuccessor.denoteWith,hs,hq,naturalSum_finite]
  rfl

theorem padValues : PadValues := by
  intro Γ p ρ a q
  obtain ⟨av,ha,h0,h1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  obtain ⟨qv,hq,hqs,_⟩ := StandardSourceFacts.Proof.groundFacts Γ p ρ q
  have hv := pad_assignment p a q av qv ha hq
  constructor
  · rw [value1_of_assignment Phi p ρ _ _ hv]
    have hh := pad_head Phi p (valuation Phi ρ) av qv
    change expressionValue Phi ρ (padVector p av qv 1)=paddedHead (expressionValue Phi ρ (av 1)) at hh
    exact hh.trans (congrArg paddedHead h1)
  · apply value0_of_assignment Phi p ρ _ _ _ hv
    have hs := pad_scalar Phi p (valuation Phi ρ) av qv _ _ h0 hqs
    rw [actualNaturalSumFiniteRight] at hs
    change _=(ParametricActualCollapse.collapseWith Phi (ordinalNaturalProduct Ordinal.omega0
      (paddedHead (expressionValue Phi ρ (av 1)))+_) : Ordinal) at hs
    rwa [h1] at hs

theorem successfulOutputs : SuccessfulOutputs := by
  intro Γ p ρ a b q
  exact ⟨StandardSourceFacts.Proof.unaryFacts Γ p ρ _,StandardSourceFacts.Proof.unaryFacts Γ p ρ _,
    StandardSourceFacts.Proof.unaryFacts Γ p ρ _,StandardSourceFacts.Proof.unaryFacts Γ p ρ _,
    StandardSourceFacts.Proof.unaryFacts Γ p ρ _⟩

theorem standardCombinatorCoordinates : StandardCombinatorCoordinates :=
  ⟨successfulOutputs,combinatorValues,signedCombinatorValues,padValues⟩
end LogicLineages.PermittedControl.StandardCombinatorCoordinates.Proof
