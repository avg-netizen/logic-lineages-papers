module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Targets
open OriginalDomain
/-- Whole hardness.tex lem:functional-detector: literal fresh positive ground
alignment and literal shared-payload full-vector detector for every actual
unary source pair under every genuine original admissible valuation. No source
assignment, norm, positivity or collapse monotonicity premise is assumed. -/
def FullFunctionalDetector : Prop :=
  ∀ (Γ : List Ty) (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Γ),
    (HeadEqual ρ a b ↔ ∃ z w : Nat,
      VectorEqual (extend ρ z w) (alignedLeft a) (alignedRight b)) ∧ Detects ρ a b
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Targets
