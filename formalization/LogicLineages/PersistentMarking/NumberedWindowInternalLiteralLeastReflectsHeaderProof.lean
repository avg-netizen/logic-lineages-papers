module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastReflectsHeaderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastKeeps)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The canonical lambda head reflects to the literal certificate's
raw source through the actual stored header comparison. This is not
an inference about an unreported representative or a numeric fit. -/
theorem exact_OpenGuardedLeastReflectsHeader (L : Program 3) (ctx ty q k tag : OTerm α)
    (selected : D B Γ (programGraph (guardedLeast (headerLeast L)) (suc k) ![ctx,ty,q]))
    (header : D B Γ (unary cellHead tag k)) :
    D B Γ (unary cellHead tag q) := by
  apply programCases cellHead ![q] _
  intro β j Δ a keep found
  rw [inputsRename] at found
  rw [unaryRename]
  have value := renameInto selected j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at value
  have tagAt := renameInto header j Δ keep
  rw [unaryRename] at tagAt
  let c := ctx.relabel j
  let t := ty.relabel j
  let raw := q.relabel j
  let min := k.relabel j
  obtain ⟨row⟩ := exact_OpenAtomicLeastReport (headerLeast L) c t raw min value
  have forwarded := exact_OpenLiteralHeaderLeastKeeps L c t raw min a ⟨Derivation.conjunctionLeft row⟩ found
  have equal := valueUnique cellHead a (tag.relabel j) ![min] forwarded tagAt
  exact outputTransport cellHead a (tag.relabel j) ![raw] equal found

#print axioms exact_OpenGuardedLeastReflectsHeader
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastReflectsHeaderProof
