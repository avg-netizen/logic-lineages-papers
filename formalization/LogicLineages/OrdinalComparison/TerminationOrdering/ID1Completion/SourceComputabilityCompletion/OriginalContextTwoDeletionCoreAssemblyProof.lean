module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionOrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalContextInsertionLengthProof (nonzeroCases)
open OriginalAllPositionContextDeleteInductionCoreProof (contextNonzero)
open OriginalContextTwoDeletionInductionSyntaxProof
open OriginalContextTwoDeletionOrderProof OriginalContextTwoDeletionTransportProof
open OriginalContextTwoDeletionSuccessorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem successorKnownLater (gamma count i j a b upper lower left right : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right))) :
    Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  have hn := contextNonzero count gamma (suc (suc j)) (andLeft hf) (andLeft (andRight (andRight hf)))
  apply nonzeroCases gamma _ hn
  intro beta rho Theta head tail hrho hc
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [rowRename] at hrow'
  simp only [fieldsRename,sucRelabel] at hf'
  exact successorAt0 (gamma.relabel rho) (count.relabel rho) head tail (i.relabel rho) (j.relabel rho)
    (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hrow' hc hf'

theorem succCore (gamma count i j a b upper lower left right : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) j a b upper lower left right))) :
    Nonempty (Derivation body Delta (result (suc i) j a b upper lower left right)) := by
  apply laterSuccessorCases i j _ (andLeft (andRight hf))
  intro beta rho Theta pred hrho he
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [rowRename] at hrow'
  simp only [fieldsRename,sucRelabel] at hf'
  have hfNext := fieldsLater (gamma.relabel rho) (count.relabel rho) (suc (i.relabel rho))
    (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho)
    (j.relabel rho) (suc pred) he hf'
  have hnext := successorKnownLater (gamma.relabel rho) (count.relabel rho) (i.relabel rho) pred
    (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hrow' hfNext
  obtain ⟨he⟩ := he
  exact resultLater (suc (i.relabel rho)) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho)
    (left.relabel rho) (right.relabel rho) (suc pred) (j.relabel rho) ⟨InternalTagArithmeticSupportProof.symm he⟩ hnext
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreAssemblyProof
