module
public import LogicLineages.OrdinalComparison.WWLiteralSizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-- Exact two-sided bound in paper05 `source-syntax.tex`, Proposition
`wwsc:prop:finite`. This ranges over the existing literal syntax (even its
zero/ill-graded trees), so is stronger than restriction to admissible source
coordinates. It is not a norm bound and does not assume source admissibility. -/
def ActualLiteralPartialSizeBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
    ordinalPartialSize t ≤ ordinalLiteralWeight t ∧
      ordinalLiteralWeight t ≤ 2 ^ ordinalLiteralNodes t - 1

/-- The size-multiplier bound in the same proposition, for an actual finite
list of input coordinates and the source multiplier's n = level(X)+1. -/
def ActualLiteralMultiplierBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (h : List (OrdinalExpression (σ :: Γ))),
    2 ^ (σ.level + 1) * (h.map ordinalPartialSize).sum ≤
      2 ^ (σ.level + 1) *
        (h.map (fun t => 2 ^ ordinalLiteralNodes t - 1)).sum

end LogicLineages.OrdinalComparison.Source.Targets
