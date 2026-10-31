module
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- The target scalar language has no fresh inputs: every variable retains
its exact original component identity. A shift records one fixed closed
positive ordinal head, independently of all input valuations. -/
inductive Scalar (ι : Type) where
  | one
  | var : ι → Scalar ι
  | add : Scalar ι → Scalar ι → Scalar ι
  | shift : ClosedPositive → Scalar ι → Scalar ι

noncomputable def fixedHead (c : ClosedPositive) : Ordinal :=
  ordinalNaturalProduct Ordinal.omega0 c.evaluate.1.repr

/-- Mathematical target interpretation h_lambda(t)=psi(lambda+t).
Effectiveness of the syntax compiler and closed-head evaluator is separate
from any claim that an arbitrary structural policy function is computable. -/
noncomputable def Scalar.value {ι : Type} (ρ : ι → Nat) : Scalar ι → Nat
  | .one => 1
  | .var x => ρ x
  | .add a b => a.value ρ + b.value ρ
  | .shift c a => actualCollapse (fixedHead c + (a.value ρ : Ordinal))

/-- Executable refusing compiler. Whole source assignment construction is
not treated as an oracle; this compiler acts on its finite literal output.
A closed collapse head is structurally extracted, not semantically guessed. -/
def compileScalar {Γ : List Ty} : OrdinalExpression Γ → Option (Scalar (OrdinalComponent Γ))
  | .one => some .one
  | .var c => some (.var c)
  | .add a b => do
      let x ← compileScalar a
      let y ← compileScalar b
      pure (.add x y)
  | .collapse a b => do
      let c ← extractPositive a
      let x ← compileScalar b
      pure (.shift c x)
  | .zero | .omega | .emul _ _ => none

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
