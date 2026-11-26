module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellFailureProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenMalformedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open NumberedWindowInternalSparseFieldCell (cellGood)
open NumberedWindowInternalSparseFieldCellFailureProof (openFailure)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseDecodeSyntaxProof (unary unaryRename)
open NumberedWindowInternalSparseFieldInductionTargets (malformed nonzero someCons)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open NumberedWindowInternalSparseFieldParserOpenTableProof (rowNil rowFromStep)
open NumberedWindowInternalSparseFieldParserOpenStepProof (stepRejected)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rejectedAtSuccessor (i : OTerm α)
    (no : Nonempty (Derivation body Γ (unary cellGood z (suc i)))) :
    Nonempty (Derivation body Γ (parserGraph z (suc i))) := by
  apply programCases (scratchTable parserBase parserStep) ![i,z,z] _
  intro β j Δ old hJ table
  simp only [parserRename,zRelabel,sucRelabel]
  simp only [tripleInputsRename,zRelabel] at table
  have no' := renameInto no j Δ hJ
  simp only [unaryRename,zRelabel,sucRelabel] at no'
  exact parserOfRow z (suc (i.relabel j)) (rowFromStep z (i.relabel j) old
    table (stepRejected (i.relabel j) old no'))

private theorem rejectMalformed (n : OTerm α)
    (bad : Nonempty (Derivation body Γ (malformed n))) :
    Nonempty (Derivation body Γ (parserGraph z n)) := by
  obtain ⟨bad⟩ := bad
  have nonzeroProof : Derivation body Γ (eqn n z).not := by
    simpa only [nonzero,equalEqn] using (Derivation.conjunctionLeft bad)
  obtain ⟨rule⟩ := openFailure body α n
  have no : Nonempty (Derivation body Γ (unary cellGood z n)) :=
    closedApply ⟨Derivation.conjunctionRight rule⟩ ⟨Derivation.conjunctionRight bad⟩
  apply zeroSuccessorCases Γ n _
  · exact ⟨Derivation.explosion (Derivation.implicationElimination
      (addHyp nonzeroProof _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro β j Δ i hJ ⟨eq⟩
    rw [parserRename,zRelabel]
    have no' := renameInto no j Δ hJ
    rw [unaryRename,zRelabel] at no'
    have shifted := moveUnary cellGood z (n.relabel j) (suc i) ⟨eq⟩ no'
    exact moveUnary parser z (suc i) (n.relabel j) ⟨symm eq⟩ (rejectedAtSuccessor i shifted)

theorem nil : OpenNilRow := by
  intro body α
  exact parserOfRow (suc (z : OTerm α)) z (rowNil (body := body) (Γ := []))

theorem gap : OpenMalformedRow := by
  intro body α n
  obtain ⟨out⟩ := rejectMalformed (body := body) (Γ := [malformed n]) n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenMalformedProof
