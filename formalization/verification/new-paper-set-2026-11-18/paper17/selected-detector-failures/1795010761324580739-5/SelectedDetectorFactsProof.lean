module
public import LogicLineages.PermittedControl.SelectedFunctionalDetectorTargets
public import LogicLineages.PermittedControl.SelectedHardnessProof
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open Source.FunctionalDetector (unary shiftTwo)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem positiveValue (ctrl : Nat → Nat) (n : Nat) :
    closedValue ctrl (UnitObservation.positive n)=((n+1 : Nat) : Ordinal) := by
  induction n with
  | zero => simp [closedValue,UnitObservation.positive,ParametricSourceSuccessor.denoteWith]
  | succ n ih =>
    change ordinalNaturalSum (closedValue ctrl (UnitObservation.positive n)) 1 = _
    rw [ih]
    simpa only [Nat.cast_one] using naturalSum_finite (n+1) 1

theorem renamed_value {Γ} (ctrl : Nat → Nat) (ρ : AdmissibleSubstitution ctrl Γ)
    (z w : Nat) (e : OrdinalExpression Γ) :
    expressionValue ctrl (extend ctrl ρ z w) (ordinalExpressionRename (shiftTwo Γ) e)=
      expressionValue ctrl ρ e := by
  rw [expressionValue,ordinalExpressionRename,ParametricSourceSuccessor.Proof.exactSubstitution]
  rfl

theorem extension_here {Γ} (ctrl : Nat → Nat) (ρ : AdmissibleSubstitution ctrl Γ) (n : Nat) :
    valuation ctrl (groundExtension ctrl ρ n) ⟨.ground,.here,0⟩=((n+1 : Nat) : Ordinal) :=
  positiveValue ctrl n

theorem source_facts {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (a : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution ctrl Γ) :
    ∃ v : OrdinalVector Γ 1, ∃ n : Nat,
      assignment p a=some v ∧ expressionValue ctrl ρ (v 0)=(n : Ordinal) ∧ 0<n ∧
      0<expressionValue ctrl ρ (v 1) ∧ expressionValue ctrl ρ (v 1)<epsilonZero ∧
      actualOrdinalNorm (expressionValue ctrl ρ (v 1))≤n := by
  obtain ⟨v,hv,h0,h1,hp0,hp1,he,hn⟩ :=
    SelectedHardnessCoordinatesProof.coordinateFacts ctrl K hc Γ p ρ a
  refine ⟨v,SelectedHardness.value0 ctrl p ρ a,hv,h0,hp0,?_,?_,?_⟩
  · simpa only [h1] using hp1
  · simpa only [h1] using he
  · simpa only [h1] using hn

theorem ground_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ .ground)
    (v : OrdinalVector Γ 0) (n : Nat) (ha : assignment p a=some v)
    (hn : expressionValue ctrl ρ (v 0)=(n : Ordinal)) : groundValue ctrl p ρ a=n := by
  unfold groundValue
  rw [ha]
  change finiteValue (expressionValue ctrl ρ (v 0))=n
  rw [hn]
  exact (SourceScalarCalibrationProof.natural_calibration n).1

theorem ground_facts {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (p : Policy) (a : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution ctrl Γ) :
    ∃ v : OrdinalVector Γ 0, assignment p a=some v ∧
      expressionValue ctrl ρ (v 0)=(groundValue ctrl p ρ a : Ordinal) ∧
      0<groundValue ctrl p ρ a := by
  obtain ⟨v,hv,hcode,hgen,hgrade,hbound⟩ :=
    SelectedCanonicalDomainProof.canonicalAssignment ctrl K hc Γ .ground p a
  obtain ⟨n,hp,hn,hfinite,hnorm⟩ :=
    (SelectedGradedPositivityProof.positiveScalars ctrl K hc).2 Γ (v 0) (hgrade 0) ρ
  have he := ground_of_assignment ctrl p ρ a v n hv hn
  refine ⟨v,hv,?_,?_⟩
  · rw [he]
    exact hn
  · rw [he]
    exact hp

theorem headEqual_iff {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary)
    (av bv : OrdinalVector Γ 1) (ha : assignment p a=some av) (hb : assignment p b=some bv) :
    HeadEqual ctrl p ρ a b ↔ expressionValue ctrl ρ (av 1)=expressionValue ctrl ρ (bv 1) := by
  constructor
  · rintro ⟨v,w,hv,hw,h⟩
    have he := Option.some.inj (ha.symm.trans hv)
    have hf := Option.some.inj (hb.symm.trans hw)
    cases he; cases hf
    exact h
  · exact fun h => ⟨av,bv,ha,hb,h⟩

theorem vectorEqual_iff {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary)
    (av bv : OrdinalVector Γ 1) (ha : assignment p a=some av) (hb : assignment p b=some bv) :
    VectorEqual ctrl p ρ a b ↔ ∀j, expressionValue ctrl ρ (av j)=expressionValue ctrl ρ (bv j) := by
  constructor
  · rintro ⟨v,w,hv,hw,h⟩
    have he := Option.some.inj (ha.symm.trans hv)
    have hf := Option.some.inj (hb.symm.trans hw)
    cases he; cases hf
    exact h
  · exact fun h => ⟨av,bv,ha,hb,h⟩
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
