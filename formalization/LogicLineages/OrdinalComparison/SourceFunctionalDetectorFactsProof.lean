module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionScalarProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProfileProof
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem source_facts {Γ} (a : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Γ) :
    ∃ v : OrdinalVector Γ 1, ∃ n : Nat,
      assignment OrdinalSyntax.defaultPolicy a=some v ∧
      expressionValue ρ (v 0)=(n:Ordinal) ∧ 0<n ∧
      0<expressionValue ρ (v 1) ∧ expressionValue ρ (v 1)<epsilonZero ∧
      actualOrdinalNorm (expressionValue ρ (v 1))≤n := by
  obtain ⟨v,hv,hg,hb⟩ := originalSourceAssignmentBounded Γ unary OrdinalSyntax.defaultPolicy a
  obtain ⟨n,hn⟩ := originalAmbientScalarFinite Γ (v 0) (hg 0) ρ
  have hp := originalScalarPositiveValue Γ (v 0) (hg 0) ρ
  rw [hn,originalFiniteValueCalibration] at hp
  have hnorm := (originalBoundedVectorSupportBridge Γ 1 v).mpr hb ρ 1
  change actualOrdinalNorm (expressionValue ρ (v 1)) ≤ actualOrdinalNorm (expressionValue ρ (v 0)) at hnorm
  rw [hn,(finiteNorm n).2] at hnorm
  exact ⟨v,n,hv,hn,hp,originalAmbientGradePositive Γ 1 (v 1) (hg 1) ρ,
    originalExpressionValueBelowEpsilonZero Γ ρ (v 1),hnorm⟩

theorem extension_here {Γ} (ρ : AdmissibleSubstitution Γ) (n : Nat) :
    valuation (groundExtension ρ n) ⟨.ground,.here,0⟩=((n+1:Nat):Ordinal) :=
  UnitObservation.Proof.positiveValue n

theorem extension_there {Γ σ} (ρ : AdmissibleSubstitution Γ) (n : Nat)
    (x : Variable Γ σ) (j : Fin (σ.level+1)) :
    valuation (groundExtension ρ n) ⟨σ,.there x,j⟩=valuation ρ ⟨σ,x,j⟩ := rfl

theorem renamed_value {Γ} (ρ : AdmissibleSubstitution Γ) (z w : Nat)
    (e : OrdinalExpression Γ) :
    expressionValue (extend ρ z w) (ordinalExpressionRename (shiftTwo Γ) e)=expressionValue ρ e := by
  rw [expressionValue,AbsoluteObserver.Proof.rename_value]
  rfl
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
