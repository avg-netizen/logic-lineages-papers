module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Targets
open ForwardTranslation LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- The exact closed anchor compiler succeeds; its real scalar is retained.
Uniform evaluation uses the existing genuine computable scalar program. -/
def AnchorCorrect : Prop :=
  ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (τ : Ty) (t : OriginalTerm Γ τ),
    ∃ w : OrdinalVector [] τ.level, ∃ s : Scalar (OrdinalComponent []),
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (close hΓ t) = some w ∧
      compileScalar (w 0) = some s ∧ anchorCode hΓ t = scalarCode (fun _ => 0) s ∧
      closedSourceValue (SyntaxCode.encodeTerm (close hΓ t)) = anchor hΓ t ∧
      openSourceValue (Γ.length, SyntaxCode.encodeTerm t) = anchor hΓ t ∧
      0 < anchor hΓ t ∧
      ∀ ν : OrdinalComponent [] → Ordinal, denote ν (w 0) = (anchor hΓ t : Ordinal)

/-- Whole paper09 absolute observer: all original all-ground contexts, arbitrary
source output and internal binders, full printed default assignment, explicit
fresh-witness formula with old shared names unchanged, and computed closed
anchor. No assumed head agreement, injectivity or source-evaluator premise. -/
def FullAbsoluteObserver : Prop :=
  Computable openSourceValue ∧ Computable closedSourceValue ∧ Source.Targets.EncodedScalarComputable ∧ AnchorCorrect ∧
  ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (τ : Ty) (t : OriginalTerm Γ τ)
    (ρ : OrdinalComponent Γ → Nat) (v : Nat),
    Formula hΓ t ρ v ↔
      ∃ w : OrdinalVector Γ τ.level,
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some w ∧
        denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (w 0) = (v : Ordinal)
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Targets
