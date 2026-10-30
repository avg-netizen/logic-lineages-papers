module
public import LogicLineages.OrdinalComparison.WWTypedComponentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-! Paper05 foundations.tex305–354: a bounded hygienic typed-vector interface.
Named-source/de Bruijn correspondence and the canonical assignment remain
separate obligations, as does all encoded computability. -/
def ActualTypedOrdinalVariableVector : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (v : Variable Γ σ),
    (ordinalVariableVector v).length = σ.level + 1 ∧
      ∀ i : Fin (σ.level + 1), (ordinalVariableVector v)[i.val]? =
        some (.var ⟨σ, v, i⟩)

def ActualTypedOrdinalRenaming : Prop :=
  (∀ (Γ : List Ty) (t : OrdinalExpression Γ),
    ordinalExpressionRename (fun v => v) t = t) ∧
  (∀ (Γ Δ Ξ : List Ty) (ρ : Renaming Γ Δ) (π : Renaming Δ Ξ)
      (t : OrdinalExpression Γ),
    ordinalExpressionRename π (ordinalExpressionRename ρ t) =
      ordinalExpressionRename (fun v => π (ρ v)) t)

def ActualTypedOrdinalVectorRenaming : Prop :=
  ∀ (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (σ : Ty) (v : Variable Γ σ),
    (ordinalVariableVector v).map (ordinalExpressionRename ρ) =
      ordinalVariableVector (ρ v)

def ActualTypedOrdinalHeadClosure : Prop :=
  (∀ (Γ : List Ty) (σ : Ty) (i : Fin (σ.level + 1)),
    ordinalHeadClosureComponent (Γ := Γ) (σ := σ) ⟨σ, .here, i⟩ = .one) ∧
  (∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression Γ),
    ordinalHeadClosure (ordinalExpressionRename (Renaming.weaken Γ σ) t) = t)

end LogicLineages.OrdinalComparison.Source.Targets
