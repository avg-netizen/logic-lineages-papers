module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenSlotProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxExchangeMemoOpenTableChecks (exact_OpenSelectedMemoLookup)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt offsetAt measureAt)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeDifferenceProof (differenceEquation)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem measureValue (R : Program 4) (slot : Nat) (child val prior old : OTerm α)
    (field : Nonempty (Derivation body Γ (programGraph (childAt slot) child ![prior,old,z,z])))
    (small : Nonempty (Derivation body Γ (ltF child (suc prior))))
    (row : Nonempty (Derivation body Γ (readRow R val child)))
    (table : Nonempty (Derivation body Γ (tableAt R old prior))) :
    Nonempty (Derivation body Γ (programGraph (measureAt slot) val ![prior,old,z,z])) := by
  apply programCases subtract ![child,prior] _
  intro β j Δ delta hJ oldDifference
  simp only [programRename,quadInputsRename,zRelabel]
  simp only [binaryInputsRename] at oldDifference
  have field' := renameInto field j Δ hJ
  have bound' := renameInto small j Δ hJ
  have row' := renameInto row j Δ hJ
  have table' := renameInto table j Δ hJ
  simp only [programRename,quadInputsRename,zRelabel] at field'
  simp only [orderRename,sucRelabel] at bound'
  simp only [readRow,programRename,tripleInputsRename,zRelabel] at row'
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at table'
  let child' := child.relabel j
  let prior' := prior.relabel j
  let old' := old.relabel j
  let xs : Fin 4 → OTerm β := ![prior',old',z,z]
  obtain ⟨sum⟩ := differenceEquation child' prior' delta bound' oldDifference
  have moved := headTransport (scratchTable (constantZero 2) R) old' prior'
    (OrdinaryArithmetic.addTerm child' delta) ![z,z] ⟨symm sum⟩ table'
  have hit := exact_OpenSelectedMemoLookup R body β Δ (val.relabel j) child' delta old' row' moved
  have offset : Nonempty (Derivation body Δ (programGraph (offsetAt slot) delta xs)) :=
    binaryGraph subtract (childAt slot) (.projection 0) delta child' prior' xs oldDifference
      field' (projectionValue 0 xs)
  exact binaryGraph lookup (offsetAt slot) (.projection 1) (val.relabel j) delta old' xs
    hit offset (projectionValue (1 : Fin 4) xs)

theorem slotReports (R : Program 4) (slot : Nat) (child val prior old : OTerm α)
    (key : Nonempty (Derivation body Γ (programGraph currentKey (suc prior) ![prior,old,z,z])))
    (field : Nonempty (Derivation body Γ (programGraph (childAt slot) child ![prior,old,z,z])))
    (small : Nonempty (Derivation body Γ (ltF child (suc prior))))
    (row : Nonempty (Derivation body Γ (readRow R val child)))
    (table : Nonempty (Derivation body Γ (tableAt R old prior))) :
    Nonempty (Derivation body Γ (programGraph (earlierAt slot) (suc z) ![prior,old,z,z])) ∧
    Nonempty (Derivation body Γ (programGraph (measureAt slot) val ![prior,old,z,z])) := by
  exact ⟨binaryGraph ltTest (childAt slot) currentKey (suc z) child (suc prior) ![prior,old,z,z]
      (acceptOfLess child (suc prior) small) field key,
    measureValue R slot child val prior old field small row table⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenSlotProof
