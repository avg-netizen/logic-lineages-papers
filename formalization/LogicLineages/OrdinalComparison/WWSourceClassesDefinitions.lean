module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.SourceTypeSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses

/-- Recursor absence is tested on the literal complete source, not a beta
normal form or just the result type. -/
def recursorFree {Γ : List Ty} {τ : Ty} : OriginalTerm Γ τ → Bool
  | .var _ | .zeroC | .succC | .caseC _ => true
  | .recC _ => false
  | .app f a => recursorFree f && recursorFree a
  | .lam body => recursorFree body
  | .ranked s _ => nomatch s

/-- Exact existing support includes every internal type and all its subtypes.
The all-ground free-context hypothesis is stated separately at source-facing
endpoints; it is not silently inferred from the output type. -/
def InternalLevelBound {Γ : List Ty} {τ : Ty} (L : Nat) (t : OriginalTerm Γ τ) : Prop :=
  ∀ σ ∈ SourceTypeSupport.typeSupport t, σ.level ≤ L

/-- Literal Omega absence; the implicit omega in a scalar collapse operation
is not a literal Omega node in a generated positive field. -/
def noOmega {Γ : List Ty} : OrdinalExpression Γ → Bool
  | .omega => false
  | .var _ | .zero | .one => true
  | .add f g | .emul f g | .collapse f g => noOmega f && noOmega g

/-- Independent structural graded height. Exponential/collapse heads spend
one level; addition and the tails do not. It never inspects ordinal values,
partial outcomes, or a chosen policy's computed trees. -/
def headHeight {Γ : List Ty} : OrdinalExpression Γ → Nat
  | .var _ | .zero | .one | .omega => 0
  | .add f g => max (headHeight f) (headHeight g)
  | .emul f g | .collapse f g => max (headHeight f + 1) (headHeight g)

end LogicLineages.OrdinalComparison.Source.SourceClasses
