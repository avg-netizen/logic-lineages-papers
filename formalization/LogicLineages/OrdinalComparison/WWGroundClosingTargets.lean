module
public import LogicLineages.OrdinalComparison.WWGroundClosingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosing.Targets

/-- Literal ground-zero closing commutes with the whole-free-first partial,
under fresh lifted binders, for every policy. No assumed substitution lemma. -/
def PartialNaturality : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (r : GroundMap Γ Δ)
    (p : AdmissibleSum.Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    AdmissiblePartial.run p i (expression r.lift t) =
      (AdmissiblePartial.run p i t).map (partialVector r)

/-- Actual capture-avoiding source substitution, through all native constructors
and arbitrary nested binder types, agrees with the full assignment. This is
an auxiliary source-closing bridge, not the whole absolute observer theorem. -/
def AssignmentNaturality : Prop :=
  ∀ (Γ Δ : List Ty) (τ : Ty) (r : GroundMap Γ Δ)
    (p : AdmissibleSum.Policy) (t : OriginalTerm Γ τ),
    AdmissibleAssignment.assignment p (t.substitute r.source) =
      (AdmissibleAssignment.assignment p t).map (vector r)
end LogicLineages.OrdinalComparison.Source.GroundClosing.Targets
