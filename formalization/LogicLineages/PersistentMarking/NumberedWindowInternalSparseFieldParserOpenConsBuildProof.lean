module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairOrderProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsBuildProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (consEquation)
open NumberedWindowInternalSparsePairOrderProof (consTailDecrease)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary certifiedCellRename)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalSparseFieldCellSuccessProof (consToCell)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open NumberedWindowInternalSparseFieldParserOpenTableProof (rowFromStep)
open NumberedWindowInternalSparseFieldParserOpenStepProof (stepCertified)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem successorFromRow (o i h t r : OTerm α)
    (tail : Nonempty (Derivation body Γ (rowGraph r t)))
    (bound : Nonempty (Derivation body Γ (ltF t (suc i))))
    (cert : Nonempty (Derivation body Γ (certifiedCell (suc i) h t)))
    (result : Nonempty (Derivation body Γ (prependGraph o h r))) :
    Nonempty (Derivation body Γ (parserGraph o (suc i))) := by
  apply programCases (scratchTable parserBase parserStep) ![i,z,z] _
  intro β j Δ old hJ table
  simp only [parserRename,sucRelabel]
  simp only [tripleInputsRename,zRelabel] at table
  have tail' := renameInto tail j Δ hJ
  have bound' := renameInto bound j Δ hJ
  have cert' := renameInto cert j Δ hJ
  have result' := renameInto result j Δ hJ
  rw [rowRename] at tail'
  rw [orderRename,sucRelabel] at bound'
  rw [certifiedCellRename,sucRelabel] at cert'
  rw [prependRename] at result'
  let ii := i.relabel j
  let oo := o.relabel j
  have made := stepCertified oo ii old (h.relabel j) (t.relabel j) (r.relabel j)
    table tail' bound' cert' result'
  exact parserOfRow oo (suc ii) (rowFromStep oo ii old table made)

theorem consFromPrepend (o n h t r : OTerm α)
    (owner : Nonempty (Derivation body Γ (consGraph n h t)))
    (tail : Nonempty (Derivation body Γ (parserGraph r t)))
    (result : Nonempty (Derivation body Γ (prependGraph o h r))) :
    Nonempty (Derivation body Γ (parserGraph o n)) := by
  let i := pairTerm h t
  obtain ⟨eq⟩ := consEquation n h t owner
  have canonical : Nonempty (Derivation body Γ (consGraph (suc i) h t)) :=
    NumberedWindowInternalSparsePairGraphProof.consGraph h t
  obtain ⟨ordered⟩ := closedApply (consTailDecrease body α (suc i) h t) canonical
  have forward := successorFromRow o i h t r (rowOfParser r t tail)
    ⟨Derivation.conjunctionRight ordered⟩ (consToCell (suc i) h t canonical) result
  exact moveUnary parser o (suc i) n ⟨symm eq⟩ forward

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsBuildProof
