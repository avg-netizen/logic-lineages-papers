module
public import LogicLineages.OrdinalComparison.UnitScalarEvaluationCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode.Targets
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactRefusingExtraction : Prop := ∀ (Γ : List Ty) (q : OrdinalExpression Γ),
  scalarCode (OrdinalSyntax.typedCode q) =
    (compileScalar (UnitHeadEvaluation.unitSyntax q)).map
      (scalarSyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1)) ∧
  valueCode (OrdinalSyntax.typedCode q) =
    (compileScalar (UnitHeadEvaluation.unitSyntax q)).map (fun s => s.value (fun _ => 1))

def EffectiveGeneratedScalar : Prop :=
  Primrec scalarCode ∧ Computable valueCode ∧
  ∀ (Γ : List Ty) (q : OrdinalExpression Γ), GeneratedOrdinalGrade Γ 0 q →
    ∃ c : Nat, valueCode (OrdinalSyntax.typedCode q) = some c ∧
      (c : Ordinal) = denote (fun _ => 1) q

/-- In particular this supplies the real scalar c of the auxiliary-ground-closed
unary K. The theorem is stronger in result type, but does not close or alter
any independent original B or C source. -/
def ActualClosedSourceScalar : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ (u : OrdinalVector Γ τ.level) (c : Nat),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.closeGround t) =
      some (GroundClosing.vector (UnaryCarrier.groundMap Γ) u) ∧
    valueCode (OrdinalSyntax.typedCode (u 0)) = some c ∧
    (c : Ordinal) = denote (fun _ => 1) (u 0) ∧
    ∀ μ : Variable Γ .ground → Nat,
      OriginalDomain.expressionValue (UnitObservation.substitution μ)
        ((GroundClosing.vector (UnaryCarrier.groundMap Γ) u) 0) = (c : Ordinal)
end LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode.Targets
