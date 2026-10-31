module
public import LogicLineages.OrdinalComparison.WWSourceRenamingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRenaming.Targets

/-- Syntactic naturality of the actual whole-free-first partial under typed
capture-avoiding lifted renaming. Both success and failure are preserved;
no evaluator/partial correctness is assumed as a premise. -/
def PartialNaturality : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (r : Renaming Γ Δ)
    (p : AdmissibleSum.Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    AdmissiblePartial.run p i (ordinalExpressionRename r.lift t) =
      (AdmissiblePartial.run p i t).map (renamePartial r)

/-- Actual source assignment naturality. Renaming is type-preserving and
lifted beneath every binder; even merging old names is allowed, since no
old name becomes the fresh head. No beta reduction or policy change occurs.
This is an explicit source09 eraser bridge, not a numbered source lemma. -/
def AssignmentNaturality : Prop :=
  ∀ (Γ Δ : List Ty) (τ : Ty) (r : Renaming Γ Δ)
    (p : AdmissibleSum.Policy) (t : OriginalTerm Γ τ),
    AdmissibleAssignment.assignment p (t.rename r) =
      (AdmissibleAssignment.assignment p t).map (renameVector r)
end LogicLineages.OrdinalComparison.Source.SourceRenaming.Targets
