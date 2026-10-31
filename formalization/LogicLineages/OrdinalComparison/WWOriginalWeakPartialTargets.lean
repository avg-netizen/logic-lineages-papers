module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

/-! Genuine simultaneous partial part of repaired wwsc:thm:weak. Input is the
original norm-admissible C_i^X grammar and substitutions are the original
closed bounded B-vectors. No finite-tail monotonicity, semantic epsilon bound,
weak inequality, or output admissibility is an assumed premise. The assembled
abstraction clause and occurring-support comparison bridge remain separate. -/
def OriginalPartialWeakAndValid : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → ∃ v : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run p i t = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧
      (i = 0 → ∀ ρ : AdmissibleSubstitution Γ,
        expressionValue ρ (ordinalHeadClosure t) ≤ expressionValue ρ (v 0))

end LogicLineages.OrdinalComparison.Source.Targets
