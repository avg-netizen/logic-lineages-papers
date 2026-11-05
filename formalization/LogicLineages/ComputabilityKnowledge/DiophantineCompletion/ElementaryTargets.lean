module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryTargets
open Elementary

/-- Signed polynomial values split into two actual natural expressions.
No extraction algorithm on an extensional polynomial proof is asserted. -/
def NaturalPairRepresentation : Prop := ∀ (α : Type) (f : (α → Nat) → Int),
  IsPoly f → ∃ p q : Expr α, ∀ ν, f ν=(p.eval ν : Int)-(q.eval ν : Int)

/-- Every equality of natural expressions has an actual finite elementary
system, including arbitrary zero-valued original parameters. -/
def ExpressionSystemNormalization : Prop := ∀ (α : Type) (p q : Expr α),
  Represents {ν : α → Nat | p.eval ν=q.eval ν}

/-- Exact finite elementary characterization of a genuine Diophantine set.
The statement asserts neither bounded-universal closure nor computable
extraction from arbitrary Dioph proofs, nor source-specific size bounds. -/
def ElementarySystemNormalization : Prop := ∀ n (S : Set (Fin n → Nat)),
  Dioph S ↔ Represents S

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryTargets
