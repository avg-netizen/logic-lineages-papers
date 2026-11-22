module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowLiteralProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename unaryRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalCoverLambdaSyntaxRowOpenProof (exact_OpenCoverLambdaSyntaxRow)
open NumberedWindowInternalCoverLambdaSelectedRowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty q : OTerm α) (j : α → β) :
    (lambdaPrior ty q).relabel j = lambdaPrior (ty.relabel j) (q.relabel j) := by
  have pairRename (a b : OTerm α) :
      (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [lambdaPrior,pairRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem atUpdate (V T : Program 1) (ty q old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) (lambdaTerm ty q))))
    (table : Nonempty (Derivation body Γ (tableAt (lambdaSyntaxUpdate V T) old (lambdaPrior ty q))))
    (update : Nonempty (Derivation body Γ (programGraph (lambdaSyntaxUpdate V T) value (lambdaTape ty q old)))) :
    LambdaRowEvidence V T body Γ ty q old := by
  let R := lambdaSyntaxUpdate V T
  let p := lambdaPrior ty q
  let n := lambdaTerm ty q
  let xs := lambdaTape ty q old
  have parentRow := (projection R (suc z) n).mp parent
  have observed := exact_OpenSelectedMemoSuccessor R body α Γ value p old table update
  have same := valueUnique (scratchRow (constantZero 2) R) value (suc z) ![n,z,z] observed parentRow
  have accepted := outputTransport R value (suc z) xs same update
  have data := literalReports (body := body) (Γ := Γ) ty q old
  have earlier : Nonempty (Derivation body Γ (programGraph (earlierAt 1) (suc z) xs)) :=
    binaryGraph ltTest (childAt 1) currentKey (suc z) q n xs
      (acceptOfLess q n data.earlier) data.child data.key
  exact ⟨table,accepted,earlier,exact_OpenCoverLambdaSyntaxRow V T body α Γ ty q old table accepted⟩

private theorem withTable (V T : Program 1) (ty q old : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) (lambdaTerm ty q))))
    (table : Nonempty (Derivation body Γ (tableAt (lambdaSyntaxUpdate V T) old (lambdaPrior ty q))))
    (next : LiteralLambdaRowCase V T body Γ ty q goal) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases (lambdaSyntaxUpdate V T) (lambdaTape ty q old) goal
  intro β j Δ value keep update
  simp only [lambdaTape,quadInputsRename,priorRename,zRelabel] at update
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,lambdaTerm,namedRename] at parent'
  simp only [tableAt,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact next β j Δ (old.relabel j) keep
    (atUpdate V T (ty.relabel j) (q.relabel j) (old.relabel j) value parent' table' update)

theorem exact_OpenCoverLambdaSelectedRow : ExactOpenCoverLambdaSelectedRow := by
  intro V T body α Γ ty q goal parent next
  let R := lambdaSyntaxUpdate V T
  apply programCases (scratchTable (constantZero 2) R) ![lambdaPrior ty q,z,z] goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  have parent' := renameInto parent j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,lambdaTerm,namedRename] at parent'
  apply withTable V T (ty.relabel j) (q.relabel j) old (goal.relabel j) parent' table
  intro γ k Ξ old' retain row
  have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k p]
    exact retain (p.relabel j) (keep p hp)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old' both row

#print axioms exact_OpenCoverLambdaSelectedRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowLiteralProof
