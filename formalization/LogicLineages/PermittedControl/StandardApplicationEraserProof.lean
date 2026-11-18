module
public import LogicLineages.PermittedControl.StandardApplicationEraserTargets
public import LogicLineages.PermittedControl.StandardSourceFactsProof
public import LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardApplicationEraser.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open SelectedFunctionalDetector (groundValue)
open SelectedHardness (value0 value1)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
theorem ground_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ .ground)
    (v : OrdinalVector Γ 0) (n : Nat) (ha : assignment p a=some v)
    (hn : expressionValue ctrl ρ (v 0)=(n : Ordinal)) : groundValue ctrl p ρ a=n := by
  unfold groundValue
  rw [ha]
  change finiteValue (expressionValue ctrl ρ (v 0))=n
  rw [hn]
  exact (SourceScalarCalibrationProof.natural_calibration n).1

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


theorem zeroCalibration : ZeroCalibration := by
  intro Γ p ρ
  refine ⟨StandardSourceFacts.Proof.groundFacts Γ p ρ _,?_⟩
  apply ground_of_assignment Phi p ρ _ (fun _ => .one) 1 rfl
  simp only [expressionValue,ParametricSourceSuccessor.denoteWith,Nat.cast_one]

theorem applicationCalibration : ApplicationCalibration := by
  intro Γ p ρ a q
  refine ⟨StandardSourceFacts.Proof.groundFacts Γ p ρ _,?_⟩
  obtain ⟨av,ha,h0,h1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  obtain ⟨qv,hq,hqs,hqp⟩ := StandardSourceFacts.Proof.groundFacts Γ p ρ q
  have hv := SelectedHardnessCombinatorSyntaxProof.app_assignment p a q av qv ha hq
  have hs := unary_app_value Phi p (valuation Phi ρ) av qv
    (value0 Phi p ρ a) (groundValue Phi p ρ q) h0 hqs
  rw [actualNaturalSumFiniteRight] at hs
  change _=(ParametricActualCollapse.collapseWith Phi
    (ordinalNaturalProduct Ordinal.omega0 (expressionValue Phi ρ (av 1))+_) : Ordinal) at hs
  rw [h1] at hs
  exact ground_of_assignment Phi p ρ _ _ _ hv hs
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

theorem eraser_value {Γ} 
    (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ .ground) :
    groundValue Phi p ρ (SourceCollisionCompletion.eraser a b)=
      ParametricActualCollapse.collapseWith Phi (Ordinal.omega0+
        ((3*groundValue Phi p ρ a+groundValue Phi p ρ b+2 : Nat) : Ordinal)) := by
  obtain ⟨av,ha,h0,hp⟩ := StandardSourceFacts.Proof.groundFacts Γ p ρ a
  obtain ⟨bv,hb,h1,hq⟩ := StandardSourceFacts.Proof.groundFacts Γ p ρ b
  have hla := SelectedHardnessUnusedProof.unused_assignment p a av ha
  have hh : SelectedHardnessUnusedProof.unusedVector p av 1=.one := by
    change AdmissibleSum.expand (p.shape .positiveAbstraction 0)
      (fun i : Fin 1 => SelectedHardnessUnusedProof.freePart av i (1 : Fin 2))=.one
    have hs := ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1 (p.shape .positiveAbstraction 0)
    rw [hs]
    rfl
  have hs : expressionValue Phi ρ (SelectedHardnessUnusedProof.unusedVector p av 0)=
      ((3*groundValue Phi p ρ a+2 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ParametricSourceSuccessor.denoteWith Phi (valuation Phi ρ)
      (repeated p .scalarRepeat 2 (.add (av 0) .one))) (expressionValue Phi ρ (av 0))=_
    have hplus : ParametricSourceSuccessor.denoteWith Phi (valuation Phi ρ) (.add (av 0) .one)=
        ((groundValue Phi p ρ a+1 : Nat) : Ordinal) := by
      change ordinalNaturalSum (expressionValue Phi ρ (av 0)) 1=_
      rw [h0]
      simpa only [Nat.cast_one] using naturalSum_finite (groundValue Phi p ρ a) 1
    rw [SelectedHardnessScalarSyntaxProof.repeated_value Phi p _ _ _ _ hplus,h0,naturalSum_finite]
    congr 1
    omega
  have hv := SelectedHardnessCombinatorSyntaxProof.app_assignment p _ b _ bv hla hb
  have hvv := unary_app_value Phi p (valuation Phi ρ)
    (SelectedHardnessUnusedProof.unusedVector p av) bv _ _ hs h1
  have hreplace := congrArg (fun u : OrdinalExpression Γ =>
    (ParametricActualCollapse.collapseWith Phi (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (ParametricSourceSuccessor.denoteWith Phi (valuation Phi ρ) u))
      (((3*groundValue Phi p ρ a+2)+groundValue Phi p ρ b : Nat) : Ordinal)) : Ordinal)) hh
  have hvv := hvv.trans hreplace
  change _=(ParametricActualCollapse.collapseWith Phi
    (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
      (((3*groundValue Phi p ρ a+2)+groundValue Phi p ρ b : Nat) : Ordinal)) : Ordinal) at hvv
  have ho := omega_one
  rw [ho,actualNaturalSumFiniteRight] at hvv
  rw [show 3*groundValue Phi p ρ a+2+groundValue Phi p ρ b=
    3*groundValue Phi p ρ a+groundValue Phi p ρ b+2 by omega] at hvv
  exact ground_of_assignment Phi p ρ _ _ _ hv hvv

theorem eraserCalibration : EraserCalibration := by
  intro Γ p ρ a b
  exact ⟨StandardSourceFacts.Proof.groundFacts Γ p ρ _,eraser_value p ρ a b⟩

theorem standardApplicationEraser : StandardApplicationEraser :=
  ⟨zeroCalibration,applicationCalibration,eraserCalibration⟩
end LogicLineages.PermittedControl.StandardApplicationEraser.Proof
