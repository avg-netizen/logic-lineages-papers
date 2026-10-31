module
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentBoundTargets
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum LiteralPartialDomain

def ActualLiteralPartialDomain : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    Domain Γ σ i t ↔ ∃ v, AdmissiblePartial.run p i t = some v

def ActualLiteralPartialUniqueBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    Domain Γ σ i t → ∃! v : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run p i t = some v ∧
        ∀ j, ordinalLiteralNodes (v j) ≤ 6 * 3 ^ ordinalLiteralNodes t

/-- Repaired Proposition wwsc:prop:finite. The exact source literal recursion
has uniquely determined finite partials with the explicit computable E bound;
the original typed source has unique finite assignments with the explicit
policy-free structural Nat sourceBound; values for a fixed partial input are
independent of output association. The structural policy generality is
stronger than the source's computable-policy restriction. No policy evaluator,
ordinal evaluation or original norm theorem is assumed or asserted. -/
def ActualRepairedFiniteExpansion : Prop :=
  ActualLiteralPartialDomain ∧ ActualLiteralPartialUniqueBound ∧
    ActualAdmissibleUniqueBoundedAssignment ∧ ActualAdmissiblePartialValue

end LogicLineages.OrdinalComparison.Source.Targets
