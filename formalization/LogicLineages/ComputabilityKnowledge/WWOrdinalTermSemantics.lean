module

public import LogicLineages.ComputabilityKnowledge.PositiveExpression
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section

/-! Literal Wilken–Weiermann (2012), Definition 2.1 syntax and Definition 2.4
interpretation. A variable type names individual source ordinal variables.
For the positive-expression embedding, each variable is the sole component
of a distinct ground-type source variable vector. Arbitrary valuations below
are totalized ordinal valuations; this file does not assert original admissible
substitution coverage or below-epsilon-zero closure for all terms.

Crucially, finite-valued O includes collapse expressions. The embedding below
is only the literal positive exponential subgrammar, not a compiler for all
finite-valued O or a resolution of paper02 cor:consumers' source-scope gap. -/
namespace LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

open PositiveExpression
open LogicLineages.OrdinalComparison

inductive Term (ι : Type) where
  | var : ι → Term ι
  | zero : Term ι
  | one : Term ι
  | omega : Term ι
  | add : Term ι → Term ι → Term ι
  | emul : Term ι → Term ι → Term ι
  | collapse : Term ι → Term ι → Term ι
  deriving DecidableEq

noncomputable def denote {ι : Type} (ρ : ι → Ordinal.{0}) : Term ι → Ordinal.{0}
  | .var i => ρ i
  | .zero => 0
  | .one => 1
  | .omega => Ordinal.omega0
  | .add a b => ordinalNaturalSum (denote ρ a) (denote ρ b)
  | .emul a b => ordinalNaturalProduct ((2 : Ordinal) ^ denote ρ a) (denote ρ b)
  | .collapse a b => (actualCollapse
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (denote ρ a)) (denote ρ b)) : Ordinal)

def substitute {ι κ : Type} (σ : ι → Term κ) : Term ι → Term κ
  | .var i => σ i
  | .zero => .zero
  | .one => .one
  | .omega => .omega
  | .add a b => .add (substitute σ a) (substitute σ b)
  | .emul a b => .emul (substitute σ a) (substitute σ b)
  | .collapse a b => .collapse (substitute σ a) (substitute σ b)

def embed {ι : Type} : Expr ι → Term ι
  | .one => .one
  | .var i => .var i
  | .add a b => .add (embed a) (embed b)
  | .emul a b => .emul (embed a) (embed b)

end LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
