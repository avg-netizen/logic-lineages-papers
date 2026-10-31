module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open OriginalDomain

def ActualScalarTotal : Prop :=
  ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground), ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
    ∀ ρ : AdmissibleSubstitution Γ,
      denote (valuation ρ) (v 0) = (rawScalar (valuation ρ) t : Ordinal) ∧
      0 < rawScalar (valuation ρ) t

/-- The displayed original unused-binder eraser equation, on arbitrary actual
sources and the full original admissible-vector domain, not only ground-free
contexts. No eraser/evaluator correctness premise appears. -/
def ActualGroundEraser : Prop :=
  ∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ),
    rawScalar (valuation ρ) (eraser p q) =
      g (3 * rawScalar (valuation ρ) p + rawScalar (valuation ρ) q + 2)

/-- Whole paper09 lem:collision, including actual source total/positive scalar
and eraser suppliers. Both total admissible contexts and exact supported
original valuations are covered. Every occurrence uses the same valuation;
functional free names, internal types and recursors are unrestricted. -/
def FullSourceCollision : Prop :=
  ActualScalarTotal ∧ ActualGroundEraser ∧
  (∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ),
    CollisionAt (valuation ρ) p q) ∧
  (∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground) (S : VariableName Γ → Prop)
    (ρ : SupportedSubstitution Γ S), CollisionAt (supportedValuation ρ) p q)
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Targets
