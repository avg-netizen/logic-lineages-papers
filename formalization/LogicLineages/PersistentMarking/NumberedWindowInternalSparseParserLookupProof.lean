module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserDropProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserLookupProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (lookupGraph lookupRename)
open ID1Completion.InternalRawListRecursionSupportProof (lookupValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subGraph subGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseParserTableLocalProof
open NumberedWindowInternalSparseParserDropSyntaxProof (tableReportRename)
open NumberedWindowInternalSparseParserDropProof (exact_OriginalSparseParserTableDropAtDifference)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rowReportRename {β : Type} (B : Program 2) (R : Program 4) (out index : OTerm α)
    (params : Fin 2 → OTerm α) (j : α → β) :
    (rowReport B R out index params).relabel j =
      rowReport B R (out.relabel j) (index.relabel j) (fun i => (params i).relabel j) := by
  simp only [rowReport,programRename,consTermRename]

/-- Lookup by the true original difference reaches the actual row of the
same original parser table. The fresh low table output is opened in the
original calculus and is used both as drop output and as head input. -/
theorem exact_OriginalSparseParserLookupAtDifference (B : Program 2) (R : Program 4)
    (lo hi gap row large : OTerm α) (params : Fin 2 → OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF lo (suc hi))))
    (difference : Nonempty (Derivation body Γ (subGraph gap lo hi)))
    (low : Nonempty (Derivation body Γ (rowReport B R row lo params)))
    (high : Nonempty (Derivation body Γ (tableReport B R large hi params))) :
    Nonempty (Derivation body Γ (lookupGraph row gap large)) := by
  apply programCases (scratchTable B R) (Fin.cons lo params) _
  intro β j Δ small keep fresh
  rw [lookupRename]
  simp only [consTermRename] at fresh
  have bound' := renameInto bound j Δ keep
  simp only [orderRename,sucRelabel] at bound'
  have difference' := renameInto difference j Δ keep
  rw [subGraphRename] at difference'
  have low' := renameInto low j Δ keep
  rw [rowReportRename] at low'
  have high' := renameInto high j Δ keep
  rw [tableReportRename] at high'
  let ps := fun i => (params i).relabel j
  have pulled := exact_OriginalSparseParserTableDropAtDifference B R
    (lo.relabel j) (hi.relabel j) (gap.relabel j) small (large.relabel j) ps
    bound' difference' fresh high'
  have head := exact_OriginalSparseParserTableHead B R (row.relabel j) small (lo.relabel j) ps low' fresh
  exact lookupValue (row.relabel j) (gap.relabel j) (large.relabel j) small pulled head

#print axioms exact_OriginalSparseParserLookupAtDifference

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserLookupProof
