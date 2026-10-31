module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitElimination.Targets
open OriginalDomain

/-- Whole finite common-unit observation elimination. The symbolic compiler
is a literal terminating syntax function; the only numeral realization uses
the genuine uniform source-code evaluator, explicitly computable on finite
lists. Source atoms in the resulting formula are actual ground sources only.
Original ground names retain one shared valuation through every deletion. -/
def FullSourceUnitElimination : Prop :=
  Computable programValues ∧
  (∀ (Γ : List Ty) (q : Tree (Nat×Nat) Γ),
    anchors (realize q)=programValues (anchors q)) ∧
  ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
    ∃ q : Tree (Nat×Nat) Γ, build (Γ.length+1) t=some q ∧
      (∀ s ∈ sources (realize q), ∀ σ ∈ s.1, σ=Ty.ground) ∧
      ∀ (ρ : Variable Γ .ground → Nat) (r : Nat),
        Eval (realize q) ρ r ↔
          ∃ v : OrdinalVector Γ τ.level,
            AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
            expressionValue (UnitObservation.substitution ρ) (v 0)=(r : Ordinal)
end LogicLineages.OrdinalComparison.Source.UnitElimination.Targets
