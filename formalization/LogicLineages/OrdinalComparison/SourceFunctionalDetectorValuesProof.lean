module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorFactsProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlgebraProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorCombinatorProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaOrderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

noncomputable def value0 {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) : Nat :=
  ((assignment OrdinalSyntax.defaultPolicy a).map (fun v => finiteValue (expressionValue ρ (v 0)))).getD 0
noncomputable def value1 {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) : Ordinal :=
  ((assignment OrdinalSyntax.defaultPolicy a).map (fun v => expressionValue ρ (v 1))).getD 0

theorem value0_of_assignment {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary)
    (av : OrdinalVector Γ 1) (n : Nat)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hn : expressionValue ρ (av 0)=(n:Ordinal)) : value0 ρ a=n := by
  unfold value0
  rw [ha]
  change finiteValue (expressionValue ρ (av 0))=n
  rw [hn]
  exact originalFiniteValueCalibration n

theorem value1_of_assignment {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary)
    (av : OrdinalVector Γ 1) (ha : assignment OrdinalSyntax.defaultPolicy a=some av) :
    value1 ρ a=expressionValue ρ (av 1) := by
  unfold value1
  rw [ha]
  rfl

theorem values_assignment {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) :
    ∃av : OrdinalVector Γ 1, assignment OrdinalSyntax.defaultPolicy a=some av ∧
      expressionValue ρ (av 0)=(value0 ρ a:Ordinal) ∧ expressionValue ρ (av 1)=value1 ρ a := by
  obtain ⟨av,n,ha,hn,_⟩ := source_facts a ρ
  exact ⟨av,ha,by rw [value0_of_assignment ρ a av n ha hn]; exact hn,
    (value1_of_assignment ρ a av ha).symm⟩

theorem values_facts {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary) :
    0<value0 ρ a ∧ 0<value1 ρ a ∧ value1 ρ a<epsilonZero ∧
      actualOrdinalNorm (value1 ρ a)≤value0 ρ a := by
  obtain ⟨av,n,ha,hn,hp,hh,he,hb⟩ := source_facts a ρ
  rw [value0_of_assignment ρ a av n ha hn,value1_of_assignment ρ a av ha]
  exact ⟨hp,hh,he,hb⟩

theorem unaryApp {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    SourceCollisionCompletion.rawScalar (valuation ρ) (.app a q)=
      appValue (value1 ρ a) (value0 ρ a) (SourceCollisionCompletion.rawScalar (valuation ρ) q) := by
  obtain ⟨av,ha,h0,h1⟩ := values_assignment ρ a
  obtain ⟨qv,hq,hqs⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ q
  have hv := unary_app_assignment a q av qv ha hq
  have hs := unary_app_value (valuation ρ) av qv (value0 ρ a)
    (SourceCollisionCompletion.rawScalar (valuation ρ) q) h0 (hqs ρ).1
  change denote (valuation ρ) (application (σ:=.ground) (τ:=.ground) OrdinalSyntax.defaultPolicy av qv 0)=_ at hs
  change expressionValue ρ (av 1)=_ at h1
  have hs' : denote (valuation ρ) (application (σ:=.ground) (τ:=.ground)
      OrdinalSyntax.defaultPolicy av qv 0)=
      (appValue (value1 ρ a) (value0 ρ a) (SourceCollisionCompletion.rawScalar (valuation ρ) q):Ordinal) := by
    rw [actualNaturalSumFiniteRight] at hs
    change _=(actualCollapse (ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ (av 1))+_):Ordinal) at hs
    rw [h1] at hs
    exact hs
  exact SourceCollisionCompletion.Proof.raw_of_assignment _ _ _ _ hv hs'

noncomputable def headCombine (a b : Ordinal) : Ordinal :=
  ordinalNaturalProduct ((2:Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (paddedHead a) (paddedHead b))

theorem combine_head {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    value1 ρ (combine a b)=headCombine (value1 ρ a) (value1 ρ b) := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment ρ b
  rw [value1_of_assignment ρ _ _ (combine_assignment a b av bv ha hb),combine_head_expression]
  change headCombine (expressionValue ρ (av 1)) (expressionValue ρ (bv 1))=_
  rw [ha1,hb1]

theorem combine_scalar {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    value0 ρ (combine a b)=
      actualCollapse (ordinalNaturalProduct Ordinal.omega0 (headCombine (value1 ρ a) (value1 ρ b))+
        ((9*value0 ρ a+5*value0 ρ b+13:Nat):Ordinal)) := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment ρ b
  apply value0_of_assignment ρ _ _ _ (combine_assignment a b av bv ha hb)
  have hs := combine_scalar_value (valuation ρ) av bv _ _ ha0 hb0
  change expressionValue ρ (combineVector av bv 0)=_ at hs
  rw [actualNaturalSumFiniteRight] at hs
  change _=(actualCollapse (ordinalNaturalProduct Ordinal.omega0
    (headCombine (expressionValue ρ (av 1)) (expressionValue ρ (bv 1)))+_):Ordinal) at hs
  rw [ha1,hb1] at hs
  exact hs
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
