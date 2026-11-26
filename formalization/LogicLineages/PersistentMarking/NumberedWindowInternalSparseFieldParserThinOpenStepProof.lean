module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenTableProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserLookupProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue successorValue programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open NumberedWindowInternalSparseFieldCellSyntaxProof (certifiedCellRename)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalSparseDecodeSyntaxProof (unary unaryRename)
open NumberedWindowInternalSparseParserLookupProof (exact_OriginalSparseParserLookupAtDifference)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atRawGraph (p : Program 1) (out i old : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out (suc i)))) :
    Nonempty (Derivation body Γ (programGraph (atRaw p) out ![i,old,z,z])) := by
  apply compositionValue p (fun _ : Fin 1 => nextRaw) out ![i,old,z,z] ![suc i] h
  intro j
  obtain rfl := Fin.eq_zero j
  apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 4)) (suc i)
    ![i,old,z,z] ![i] (successorValue ![i])
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue (0 : Fin 4) ![i,old,z,z]

theorem stepRejected (i old : OTerm α)
    (h : Nonempty (Derivation body Γ (unary cellGood z (suc i)))) :
    Nonempty (Derivation body Γ (stepGraph z i old)) :=
  zeroBranchIntro (atRaw cellGood) (constantZero 4) onCell z ![i,old,z,z]
    (atRawGraph cellGood z i old h) (zeroConstantValue ![i,old,z,z])

private theorem lookupOfActualDifference (r i old t gap : OTerm α)
    (table : Nonempty (Derivation body Γ (tableGraph old i)))
    (row : Nonempty (Derivation body Γ (rowGraph r t)))
    (bound : Nonempty (Derivation body Γ (ltF t (suc i))))
    (diff : Nonempty (Derivation body Γ (subGraph gap t i))) :
    Nonempty (Derivation body Γ (programGraph lookup r ![gap,old])) := by
  exact exact_OriginalSparseParserLookupAtDifference parserBase parserStep
    t i gap r old ![z,z] bound diff row table

private theorem stepAtDifference (o i old h t r gap : OTerm α)
    (table : Nonempty (Derivation body Γ (tableGraph old i)))
    (row : Nonempty (Derivation body Γ (rowGraph r t)))
    (bound : Nonempty (Derivation body Γ (ltF t (suc i))))
    (cert : Nonempty (Derivation body Γ (certifiedCell (suc i) h t)))
    (prepend : Nonempty (Derivation body Γ (prependGraph o h r)))
    (diff : Nonempty (Derivation body Γ (subGraph gap t i))) :
    Nonempty (Derivation body Γ (stepGraph o i old)) := by
  obtain ⟨cert⟩ := cert
  let xs : Fin 4 → OTerm α := ![i,old,z,z]
  have hg := atRawGraph cellGood (suc z) i old ⟨Derivation.conjunctionLeft cert⟩
  have hh := atRawGraph cellHead h i old ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cert)⟩
  have ht := atRawGraph cellTail t i old ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cert)⟩
  have passLag : Nonempty (Derivation body Γ (programGraph tailLag gap xs)) := by
    apply compositionValue subtract ![atRaw cellTail,.projection 0] gap xs ![t,i] diff
    intro j
    exact Fin.cases ht (Fin.cases (projectionValue (0 : Fin 4) xs) (fun k => Fin.elim0 k)) j
  have passResult : Nonempty (Derivation body Γ (programGraph priorResult r xs)) := by
    apply compositionValue lookup ![tailLag,.projection 1] r xs ![gap,old]
      (lookupOfActualDifference r i old t gap table row bound diff)
    intro j
    exact Fin.cases passLag (Fin.cases (projectionValue (1 : Fin 4) xs) (fun k => Fin.elim0 k)) j
  have passCell : Nonempty (Derivation body Γ (programGraph onCell o xs)) := by
    apply compositionValue prependResult ![atRaw cellHead,priorResult] o xs ![h,r] prepend
    intro j
    exact Fin.cases hh (Fin.cases passResult (fun k => Fin.elim0 k)) j
  exact successorBranchIntro (atRaw cellGood) (constantZero 4) onCell o z xs hg passCell

theorem stepCertified (o i old h t r : OTerm α)
    (table : Nonempty (Derivation body Γ (tableGraph old i)))
    (row : Nonempty (Derivation body Γ (rowGraph r t)))
    (bound : Nonempty (Derivation body Γ (ltF t (suc i))))
    (cert : Nonempty (Derivation body Γ (certifiedCell (suc i) h t)))
    (prepend : Nonempty (Derivation body Γ (prependGraph o h r))) :
    Nonempty (Derivation body Γ (stepGraph o i old)) := by
  apply programCases subtract ![t,i] _
  intro β j Δ gap hJ diff
  rw [stepRename]
  rw [binaryInputsRename] at diff
  have table' := renameInto table j Δ hJ
  have row' := renameInto row j Δ hJ
  have bound' := renameInto bound j Δ hJ
  have cert' := renameInto cert j Δ hJ
  have prepend' := renameInto prepend j Δ hJ
  rw [tableRename] at table'
  rw [rowRename] at row'
  rw [orderRename,sucRelabel] at bound'
  rw [certifiedCellRename,sucRelabel] at cert'
  rw [prependRename] at prepend'
  exact stepAtDifference (o.relabel j) (i.relabel j) (old.relabel j)
    (h.relabel j) (t.relabel j) (r.relabel j) gap table' row' bound' cert' prepend' diff

#print axioms stepCertified

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenStepProof
