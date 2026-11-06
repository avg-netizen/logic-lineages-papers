module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks
open SourceComputabilityFormulaSupportProof

/-- Literal empty/last-binder identities, including the original Fin order. -/
def ActualFiniteBinderEquations : Prop :=
  (∀ (α : Type) (phi : Formula (α ⊕ Fin 0)), block phi = phi.relabel eraseZero) ∧
  (∀ (α : Type) (k : Nat) (phi : Formula (α ⊕ Fin (k+1))),
    block phi = block (existsOne (phi.relabel (splitLast k))))

/-- The original ordinary arithmetic compiler block embeds into precisely
this same bounded syntax, with no changed variable order or coding. -/
def ActualOriginalBlockEmbedding : Prop :=
  ∀ (α : Type) (k : Nat) (phi : OrdinaryArithmetic.Formula (α ⊕ Fin k)),
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.existsFin phi) =
    block (arithmeticEmbedding.onFormula phi)

def ActualFiniteExistentialIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (k : Nat) (Gamma : List (Formula α))
    (phi : Formula (α ⊕ Fin k)) (ts : Fin k → Term α),
  Nonempty (Derivation body Gamma (phi.subst (Sum.elim Term.var ts))) →
  Nonempty (Derivation body Gamma (block phi))

/-- A genuine admissible finite-block elimination rule, with the original
proof of the fresh-variable branch as an explicit premise. -/
def ActualFiniteExistentialElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (k : Nat) (Gamma : List (Formula α))
    (phi : Formula (α ⊕ Fin k)) (psi : Formula α),
  Nonempty (Derivation body Gamma (block phi)) →
  Nonempty (Derivation body (phi :: Gamma.map (fun p => p.relabel Sum.inl)) (psi.relabel Sum.inl)) →
  Nonempty (Derivation body Gamma psi)

/-- Exact original finite conjunction, including the empty tuple. -/
def ActualOriginalFiniteConjunction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (k : Nat) (Gamma : List (Formula α))
    (phi : Fin k → OrdinaryArithmetic.Formula α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (OrdinaryArithmetic.andFin phi))) ↔
    ∀ i, Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (phi i)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksTargets
