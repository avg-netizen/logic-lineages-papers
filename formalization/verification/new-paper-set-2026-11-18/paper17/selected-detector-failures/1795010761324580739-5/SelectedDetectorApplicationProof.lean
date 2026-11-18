module
public import LogicLineages.PermittedControl.SelectedDetectorAlignmentProof
public import LogicLineages.PermittedControl.SelectedDetectorNumericProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaOrderProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open Source.FunctionalDetector (unary)
open SelectedHardness (value0 value1)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem values_assignment {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    ∃ av : OrdinalVector Γ 1, assignment p a=some av ∧
      expressionValue ctrl ρ (av 0)=(value0 ctrl p ρ a : Ordinal) ∧
      expressionValue ctrl ρ (av 1)=value1 ctrl p ρ a := by
  obtain ⟨v,hv,h0,h1,_⟩ := SelectedHardnessCoordinatesProof.coordinateFacts ctrl K hc Γ p ρ a
  exact ⟨v,hv,h0,h1⟩

theorem values_facts {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    0<value0 ctrl p ρ a ∧ 0<value1 ctrl p ρ a ∧ value1 ctrl p ρ a<epsilonZero ∧
      actualOrdinalNorm (value1 ctrl p ρ a)≤value0 ctrl p ρ a := by
  obtain ⟨v,hv,h0,h1,hp0,hp1,he,hn⟩ := SelectedHardnessCoordinatesProof.coordinateFacts ctrl K hc Γ p ρ a
  exact ⟨hp0,hp1,he,hn⟩

theorem unary_app_value {Γ} (ctrl : Nat → Nat) (p : Policy) (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) (a0 q0 : Nat)
    (ha : ParametricSourceSuccessor.denoteWith ctrl ν (av 0)=(a0 : Ordinal))
    (hq : ParametricSourceSuccessor.denoteWith ctrl ν (qv 0)=(q0 : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (application (σ:=.ground) (τ:=.ground) p av qv 0)=
      (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (ParametricSourceSuccessor.denoteWith ctrl ν (av 1)))
        ((a0+q0 : Nat) : Ordinal)) : Ordinal) := by
  have he : application (σ:=.ground) (τ:=.ground) p av qv 0 =
      .collapse (av 1) (.add (av 0) (qv 0)) := by
    change Term.collapse (ordinalBoxPositive 0 (@ordinalVectorAt Γ 1 av) (@ordinalVectorAt Γ 0 qv) 1)
      (boxTail p 0 (av 0) (qv 0)) = _
    rw [ordinalBoxPositive]
    simp only [show ¬(1≤0) by omega,dite_false,boxTail,if_pos rfl,ordinalVectorAt]
    rfl
  rw [he]
  simp only [ParametricSourceSuccessor.denoteWith,ha,hq,naturalSum_finite]

theorem unaryApp {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    groundValue ctrl p ρ (.app a q)=appValue ctrl (value1 ctrl p ρ a)
      (value0 ctrl p ρ a) (groundValue ctrl p ρ q) := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment ctrl K hc p ρ a
  obtain ⟨qv,hq,hqs,hqp⟩ := ground_facts ctrl K hc p q ρ
  have hv := SelectedHardnessCombinatorSyntaxProof.app_assignment p a q av qv ha hq
  have hs := unary_app_value ctrl p (valuation ctrl ρ) av qv
    (value0 ctrl p ρ a) (groundValue ctrl p ρ q) h0 hqs
  rw [actualNaturalSumFiniteRight] at hs
  change _=(ParametricActualCollapse.collapseWith ctrl
    (ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ (av 1))+_) : Ordinal) at hs
  rw [h1] at hs
  exact ground_of_assignment ctrl p ρ _ _ _ hv hs

open Vendor.R1

private theorem omega_one : ordinalNaturalProduct Ordinal.omega0 1 = Ordinal.omega0 := by
  let w : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  let o : NONote := ⟨1, ONote.nf_one⟩
  have h := naturalProductDenotation w o
  have hw : w.1.repr = Ordinal.omega0 := by simp [w,ONote.repr]
  have ho : o.1.repr = 1 := by simp [o,ONote.repr_one]
  have hp : (naturalProduct w o).1 = w.1 := by
    change rawNaturalProduct (.oadd 1 1 .zero) (.oadd .zero 1 .zero) = .oadd 1 1 .zero
    have hz (x : ONote) : rawNaturalSum x .zero = x := by
      cases x <;> rw [rawNaturalSum] <;> simp
    simp only [rawNaturalProduct,rawMonomialProduct,hz]
    congr 2
  rw [hp,hw,ho] at h
  exact h.symm

theorem eraser_value {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ .ground) :
    groundValue ctrl p ρ (SourceCollisionCompletion.eraser a b)=
      ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0+
        ((3*groundValue ctrl p ρ a+groundValue ctrl p ρ b+2 : Nat) : Ordinal)) := by
  obtain ⟨av,ha,h0,hp⟩ := ground_facts ctrl K hc p a ρ
  obtain ⟨bv,hb,h1,hq⟩ := ground_facts ctrl K hc p b ρ
  have hla := SelectedHardnessUnusedProof.unused_assignment p a av ha
  have hh : SelectedHardnessUnusedProof.unusedVector p av 1=.one := by
    change AdmissibleSum.expand (p.shape .positiveAbstraction 0)
      (fun i : Fin 1 => SelectedHardnessUnusedProof.freePart av i (1 : Fin 2))=.one
    have hs := ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1 (p.shape .positiveAbstraction 0)
    rw [hs]
    rfl
  have hs : expressionValue ctrl ρ (SelectedHardnessUnusedProof.unusedVector p av 0)=
      ((3*groundValue ctrl p ρ a+2 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ParametricSourceSuccessor.denoteWith ctrl (valuation ctrl ρ)
      (repeated p .scalarRepeat 2 (.add (av 0) .one))) (expressionValue ctrl ρ (av 0))=_
    have hplus : ParametricSourceSuccessor.denoteWith ctrl (valuation ctrl ρ) (.add (av 0) .one)=
        ((groundValue ctrl p ρ a+1 : Nat) : Ordinal) := by
      change ordinalNaturalSum (expressionValue ctrl ρ (av 0)) 1=_
      rw [h0]
      simpa only [Nat.cast_one] using naturalSum_finite (groundValue ctrl p ρ a) 1
    rw [SelectedHardnessScalarSyntaxProof.repeated_value ctrl p _ _ _ _ hplus,h0,naturalSum_finite]
    congr 1
    omega
  have hv := SelectedHardnessCombinatorSyntaxProof.app_assignment p _ b _ bv hla hb
  have hvv := unary_app_value ctrl p (valuation ctrl ρ)
    (SelectedHardnessUnusedProof.unusedVector p av) bv _ _ hs h1
  rw [hh] at hvv
  change _=(ParametricActualCollapse.collapseWith ctrl
    (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
      (((3*groundValue ctrl p ρ a+2)+groundValue ctrl p ρ b : Nat) : Ordinal)) : Ordinal) at hvv
  have ho := omega_one
  rw [ho,actualNaturalSumFiniteRight] at hvv
  rw [show 3*groundValue ctrl p ρ a+2+groundValue ctrl p ρ b=
    3*groundValue ctrl p ρ a+groundValue ctrl p ρ b+2 by omega] at hvv
  exact ground_of_assignment ctrl p ρ _ _ _ hv hvv
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
