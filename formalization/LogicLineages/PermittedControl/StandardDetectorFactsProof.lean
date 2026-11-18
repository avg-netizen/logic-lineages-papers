module
public import LogicLineages.PermittedControl.StandardFunctionalDetectorTargets
public import LogicLineages.PermittedControl.StandardCombinatorCoordinatesProof
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain SelectedFunctionalDetector
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


theorem source_facts {Γ} (p : Policy) (a : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Phi Γ) :
    ∃ v : OrdinalVector Γ 1, ∃ n : Nat,
      assignment p a=some v ∧ expressionValue Phi ρ (v 0)=(n : Ordinal) ∧ 0 < n ∧
      0 < expressionValue Phi ρ (v 1) ∧ expressionValue Phi ρ (v 1)<epsilonZero ∧
      actualOrdinalNorm (expressionValue Phi ρ (v 1))≤n := by
  obtain ⟨v,hv,h0,h1,hp0,hp1,he,hn⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  refine ⟨v,SelectedHardness.value0 Phi p ρ a,hv,h0,hp0,?_,?_,?_⟩
  · simpa only [h1] using hp1
  · simpa only [h1] using he
  · simpa only [h1] using hn

theorem extensionCalibration : ExtensionCalibration := by
  refine ⟨positiveValue Phi,?_⟩
  intro Γ ρ z w
  refine ⟨extension_here Phi _ z,?_,fun _ _ _ => rfl,renamed_value Phi ρ z w⟩
  exact extension_here Phi ρ w
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
end LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
