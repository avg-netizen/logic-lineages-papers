module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentBoundDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum AdmissibleAssignmentBound

/-- The positive aggregation estimate in the source expansion proof, for the
actual arbitrary macro shape and every unchanged operand. -/
def ActualAdmissibleAggregationBound : Prop :=
  ∀ (Γ : List Ty) (p : Policy) (m E : Nat) (xs : Fin (m + 1) → OrdinalExpression Γ),
    (∀ i, ordinalLiteralNodes (xs i) ≤ E) →
      ordinalLiteralNodes (expand (p.shape .positiveAbstraction m) xs) ≤ (m + 1) * E + m

def ActualAdmissibleAbstractionBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m N : Nat) (p : Policy)
    (h : OrdinalVector (σ :: Γ) m),
    (∀ i, ordinalLiteralNodes (h i) ≤ N) →
    ∀ v, AdmissibleAssignment.abstraction p h = some v →
      ∀ j, ordinalLiteralNodes (v j) ≤ abstractionBound (σ.level + 1) m N

def ActualAdmissibleBoxBound : Prop :=
  ∀ (Γ : List Ty) (m n A B : Nat) (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
    (∀ i, ordinalLiteralNodes (f i) ≤ A) →
    (∀ i, ordinalLiteralNodes (g i) ≤ B) →
      ∀ j, ordinalLiteralNodes (AdmissibleAssignment.box p f g j) ≤ boxBound n A B

/-- Composed bound for the whole original typed source, uniform even over
noncomputable structural policy selectors. The bound itself is the explicit
policy-free Nat recursion in Definitions, not an assumed bound field. -/
def ActualAdmissibleSourceBound : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment p t = some v →
      ∀ j, ordinalLiteralNodes (v j) ≤ sourceBound t

/-- Unique actual finite output with the explicit uniform source bound. This
is not a theorem that an arbitrary policy selector is computable. -/
def ActualAdmissibleUniqueBoundedAssignment : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
    ∃! v : OrdinalVector Γ τ.level,
      AdmissibleAssignment.assignment p t = some v ∧
        ∀ j, ordinalLiteralNodes (v j) ≤ sourceBound t

end LogicLineages.OrdinalComparison.Source.Targets
