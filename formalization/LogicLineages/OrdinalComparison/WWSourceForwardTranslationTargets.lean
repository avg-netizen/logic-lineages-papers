module
public import LogicLineages.OrdinalComparison.WWFixedShiftTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Entire repaired forward-translation content: every actual source with
only ground free names, unrestricted internal types/binders/recursors, has
closed positive final fields evaluated by the explicit normal-notation
program and a scalar output compiled by the explicit shared-input syntax
transformer. Its fixed heads are genuine positive omega*c ordinals and its
h_lambda functions have actual Computable certificates.

The finite-output compiler and closed-head evaluator are uniform and contain
no policy calls. No computability of an arbitrary Policy.shape selector, nor
uniform construction of all its source assignments without that selector,
is inferred or assumed. -/
def ActualSourceForwardTranslation : Prop :=
  ScalarFixedHeadAdmissible ∧ ScalarFixedShiftComputable ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
      ∃ v : OrdinalVector Γ τ.level,
        assignment p t = some v ∧
        (∀ j : Fin (τ.level + 1), 0 < j.val →
          ordinalExpressionVariables (v j) = [] ∧
          ∃ c : ClosedPositive, extractPositive (v j) = some c ∧
            0 < c.evaluate.1.repr ∧
            ∀ ρ : OrdinalComponent Γ → Ordinal, c.evaluate.1.repr = denote ρ (v j)) ∧
        ∃ s : Scalar (OrdinalComponent Γ), compileScalar (v 0) = some s ∧
          (∀ ρ : OrdinalComponent Γ → Nat,
            (s.value ρ : Ordinal) = denote (fun c => (ρ c : Ordinal)) (v 0)) ∧
          (∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) → 0 < s.value ρ)

end LogicLineages.OrdinalComparison.Source.Targets
