module
public import LogicLineages.OrdinalComparison.UnitScalarEvaluationCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay
open ForwardTranslation

def source {Γ : List Ty} (K : OriginalTerm Γ (Ty.curriedGround 1)) :
    OriginalTerm (.ground :: Γ) .ground :=
  .app ((UnaryCarrier.closeGround K).rename (fun x => .there x)) (.var .here)

/-- Exact total norm on the source observation ray. The real scalar c is not
replaced by a convenient numeral or removed from the argument. -/
noncomputable def totalNorm (a : ClosedPositive) (c n : Nat) : Nat :=
  actualOrdinalNorm (fixedHead a) + c + 1 + n
noncomputable def rayValue (a : ClosedPositive) (c n : Nat) : Nat :=
  actualHeadValue (fixedHead a) (totalNorm a c n)

/-- Numeric constants arise from the actual complete assignment of K. -/
def Constants {Γ : List Ty} (K : OriginalTerm Γ (Ty.curriedGround 1))
    (u : OrdinalVector Γ (Ty.curriedGround 1).level) (a : ClosedPositive) (c : Nat) : Prop :=
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy K = some u ∧
  UnitHeadEvaluation.extractUnitHead (u (UnaryCarrier.headIndex 0)) = some a ∧
  UnitScalarEvaluationCode.valueCode (OrdinalSyntax.typedCode (u 0)) = some c
end LogicLineages.OrdinalComparison.Source.ActualUnaryRay
