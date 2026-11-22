module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename unaryRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt measureAt)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty q : OTerm α) (j : α → β) :
    (lambdaPrior ty q).relabel j = lambdaPrior (ty.relabel j) (q.relabel j) := by
  have pairRename (a b : OTerm α) :
      (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [lambdaPrior,pairRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem afterRead (V T : Program 1) (ty q old value : OTerm α)
    (table : Nonempty (Derivation body Γ (tableAt (lambdaSyntaxUpdate V T) old (lambdaPrior ty q))))
    (accepted : Nonempty (Derivation body Γ
      (programGraph (lambdaSyntaxUpdate V T) (suc z) (lambdaTape ty q old))))
    (childRead : Nonempty (Derivation body Γ (readRow (lambdaSyntaxUpdate V T) value q))) :
    Nonempty (Derivation body Γ (lambdaRecovered V T ty q old)) := by
  let xs := lambdaTape ty q old
  let R := lambdaSyntaxUpdate V T
  let prior := lambdaPrior ty q
  have fields := literalReports (body := body) (Γ := Γ) ty q old
  have reads := slotReports R 1 q value prior old fields.key fields.child fields.earlier childRead table
  have guard : Nonempty (Derivation body Γ (programGraph lambdaGuard (suc z) xs)) :=
    conjunctionAccept lambdaShape (earlierAt 1) xs fields.shape reads.1
  have branch : Nonempty (Derivation body Γ (programGraph (lambdaAccept T) (suc z) xs)) :=
    successorBranchElim lambdaGuard (unaryAfter V currentKey) (lambdaAccept T) (suc z) z xs guard accepted
  obtain ⟨parts⟩ := conjunctionRecover (lambdaTypeSlot T) (measureAt 1) xs branch
  have annotation : Nonempty (Derivation body Γ (unary T (suc z) ty)) := by
    apply compositionRecover T (fun _ : Fin 1 => childAt 0) (suc z) xs ![ty]
      ⟨Derivation.conjunctionLeft parts⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact fields.annotation
  have same := valueUnique (measureAt 1) value (suc z) xs reads.2
    ⟨Derivation.conjunctionRight parts⟩
  have acceptedRead : Nonempty (Derivation body Γ (readRow R (suc z) q)) :=
    outputTransport (scratchRow (constantZero 2) R) value (suc z) ![q,z,z] same childRead
  obtain ⟨child⟩ := (projection R (suc z) q).mpr acceptedRead
  obtain ⟨annotation⟩ := annotation
  exact ⟨Derivation.conjunctionIntroduction annotation
    (Derivation.conjunctionIntroduction child (Derivation.conjunctionRight parts))⟩

theorem exact_OpenCoverLambdaSyntaxRow : ExactOpenCoverLambdaSyntaxRow := by
  intro V T body α Γ ty q old table accepted
  let R := lambdaSyntaxUpdate V T
  apply programCases (scratchRow (constantZero 2) R) ![q,z,z] _
  intro β j Δ value keep child
  simp only [tripleInputsRename,zRelabel] at child
  simp only [lambdaRecovered,conjunctionRename,unaryRename,programRename,lambdaTape,
    quadInputsRename,priorRename,zRelabel,sucRelabel]
  have table' := renameInto table j Δ keep
  have accepted' := renameInto accepted j Δ keep
  simp only [tableAt,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  simp only [programRename,lambdaTape,quadInputsRename,priorRename,zRelabel,sucRelabel] at accepted'
  exact afterRead V T (ty.relabel j) (q.relabel j) (old.relabel j) value table' accepted' child

#print axioms exact_OpenCoverLambdaSyntaxRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowOpenProof
