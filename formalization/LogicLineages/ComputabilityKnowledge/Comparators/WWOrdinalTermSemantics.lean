module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

@[expose] public section

/-! Source suppliers for paper02's actual finite-fragment embedding in the
original WW O grammar. No admissibility, C membership, or full finite-valued
O decision theorem is claimed. General structural substitution includes the
original collapse constructor and uses its actual ordinal semantics. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalTermSemantics

open PositiveExpression
open LogicLineages.OrdinalComparison
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def FiniteArithmetic : Prop :=
  ∀ a b : Nat,
    ordinalNaturalSum (a : Ordinal.{0}) (b : Ordinal.{0}) = ((a + b : Nat) : Ordinal.{0}) ∧
    ordinalNaturalProduct (a : Ordinal.{0}) (b : Ordinal.{0}) = ((a * b : Nat) : Ordinal.{0}) ∧
    (2 : Ordinal.{0}) ^ (a : Ordinal.{0}) = ((2 ^ a : Nat) : Ordinal.{0})

def FiniteNorm : Prop :=
  ∀ n : Nat, (n : Ordinal.{0}) < epsilonZero ∧ actualOrdinalNorm (n : Ordinal.{0}) = n

def LiteralEmbedding : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)) (ρ : Fin d → PosNat),
    denote (fun i => ((ρ i : Nat) : Ordinal.{0})) (embed e) = (e.eval ρ : Ordinal.{0}) ∧
    actualOrdinalNorm (denote (fun i => ((ρ i : Nat) : Ordinal.{0})) (embed e)) = e.eval ρ

def StructuralSubstitution : Prop :=
  ∀ (ι κ : Type) (σ : ι → Term κ) (ρ : κ → Ordinal.{0}) (t : Term ι),
    denote ρ (substitute σ t) = denote (fun i => denote ρ (σ i)) t

def InjectiveEmbedding : Prop :=
  ∀ ι : Type, Function.Injective (@embed ι)

def Target : Prop := FiniteArithmetic ∧ FiniteNorm ∧ LiteralEmbedding ∧
  StructuralSubstitution ∧ InjectiveEmbedding

end LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalTermSemantics
