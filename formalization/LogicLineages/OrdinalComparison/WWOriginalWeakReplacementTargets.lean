module
public import LogicLineages.OrdinalComparison.WWOriginalSupportDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

/-! Whole repaired source-syntax.tex wwsc:thm:weak. The scalar comparison uses
exactly original occurring-vector substitutions. Original norm-admissible
partial inputs produce actual C-vectors without the bound head; the same holds
for the pure assembled delta. Explicit weakening back into the old context
certifies syntactic X-freeness, not merely a value equality. All structural
policies are covered. No bounded-norm preservation or broader original F1
assignment theorem is asserted. -/
def OriginalWeakReplacement : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy),
    (∀ t : OrdinalExpression (σ :: Γ), HeadGrade Γ σ 0 t →
      ∃ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p 0 t = some v ∧
        ∀ ρ : SupportedSubstitution Γ (comparisonSupport (ordinalHeadClosure t) (v 0)),
          supportedValue ρ (ordinalHeadClosure t) ≤ supportedValue ρ (v 0)) ∧
    (∀ (i : Nat) (t : OrdinalExpression (σ :: Γ)), HeadGrade Γ σ i t →
      ∃ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p i t = some v ∧
        ∀ j, AmbientGrade Γ j.val (v j) ∧
          ordinalHeadFree (σ := σ)
            (ordinalExpressionRename (fun {_} x => Variable.there x) (v j)) = true) ∧
    (∀ (m : Nat) (h : OrdinalVector (σ :: Γ) m),
      (∀ i, HeadGrade Γ σ i.val (h i)) →
      ∃ v : OrdinalVector Γ (max (σ.level + 1) m), delta p h = some v ∧
        ∀ j, AmbientGrade Γ j.val (v j) ∧
          ordinalHeadFree (σ := σ)
            (ordinalExpressionRename (fun {_} x => Variable.there x) (v j)) = true)

end LogicLineages.OrdinalComparison.Source.Targets
