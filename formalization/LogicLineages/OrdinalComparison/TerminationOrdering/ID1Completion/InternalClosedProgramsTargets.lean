module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalFiniteBlocks InternalClosedPrograms
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

def ActualUniversalBinderEquations : Prop :=
  (∀ (α : Type) (phi : Formula (α ⊕ Fin 0)), allBlock phi = phi.relabel eraseZero) ∧
  (∀ (α : Type) (k : Nat) (phi : Formula (α ⊕ Fin (k+1))),
    allBlock phi = allBlock (allOne (phi.relabel (splitLast k))))

def ActualOriginalUniversalEmbedding : Prop :=
  ∀ (α : Type) (k : Nat) (phi : OFormula (α ⊕ Fin k)),
    arithmeticEmbedding.onFormula (OrdinaryArithmetic.forallFin phi) =
      allBlock (arithmeticEmbedding.onFormula phi)

def ActualFiniteUniversalIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (k : Nat) (Gamma : List (Formula α))
    (phi : Formula (α ⊕ Fin k)),
  Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl)) phi) →
    Nonempty (Derivation body Gamma (allBlock phi))

def ActualFiniteUniversalElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (k : Nat) (Gamma : List (Formula α))
    (phi : Formula (α ⊕ Fin k)) (ts : Fin k → Term α),
  Nonempty (Derivation body Gamma (allBlock phi)) →
    Nonempty (Derivation body Gamma (phi.subst (Sum.elim Term.var ts)))

/-- Actual CLOSED first-order theorems for the existing recursion-free
fragment, not merely a semantic statement or externally quantified family. -/
def ActualClosedOriginalProgramSentences : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (p : Program n),
  GorbowArithmeticCompositionCertificates.recursionFree p →
    Nonempty (Derivation body ([] : List (Formula Empty))
      (arithmeticEmbedding.onFormula (totalSentence p))) ∧
    Nonempty (Derivation body ([] : List (Formula Empty))
      (arithmeticEmbedding.onFormula (uniqueSentence p)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsTargets
