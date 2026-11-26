module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentLeafProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate auxAccept)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck certain earlierAt)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverAuxFragmentGuardTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem headerZeroOfNotOne (tag arity : Nat) (key : OTerm α)
    (no : Nonempty (Derivation body Γ (unary (header tag arity) (suc z) key).not)) :
    Nonempty (Derivation body Γ (unary (header tag arity) z key)) := by
  unfold header nodeGood at no ⊢
  exact conjunctionReject _ _ ![key] no

private theorem certainZero (xs : Fin 4 → OTerm α)
    (no : Nonempty (Derivation body Γ (programGraph shapeCheck z xs))) :
    Nonempty (Derivation body Γ (programGraph certain z xs)) := by
  let S := conjunction (earlierAt 2) (earlierAt 3)
  let C := programGraph certain (suc z) xs
  apply conjunctionReject shapeCheck S xs
  obtain ⟨both⟩ := conjunctionRecover shapeCheck S xs (body := body) (Gamma := C :: Γ)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := valueUnique shapeCheck (suc z) z xs ⟨Derivation.conjunctionLeft both⟩ (withHyp no C)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private theorem leafHeaderReject (raw : OTerm α)
    (actual : Nonempty (Derivation body Γ (unary fragmentLeaf (suc z) raw))) :
    Nonempty (Derivation body Γ (unary (header 2 2) z raw)) := by
  let P := unary (header 2 2) (suc z) raw
  apply formulaCases P _
  · have h : Nonempty (Derivation body (P :: Γ) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have dead := successorBranchElim (header 2 2) (constantOne 1) (constantZero 1)
      (suc z) z ![raw] h (withHyp actual P)
    obtain ⟨bad⟩ := valueUnique (constantZero 1) (suc z) z ![raw] dead (constantZeroValue ![raw])
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · exact headerZeroOfNotOne 2 2 raw ⟨Derivation.hypothesis List.mem_cons_self⟩

private theorem atPhysicalRow (prior old : OTerm α)
    (noAux : Nonempty (Derivation body Γ (unary termShape z (suc prior))))
    (step : Nonempty (Derivation body Γ
      (programGraph (auxSyntaxUpdate fragmentLeaf (constantOne 1)) (suc z) ![prior,old,z,z]))) :
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc prior))) := by
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have rejected := unaryGraph termShape currentKey z raw xs noAux key
  have pick := zeroBranchElim certain (unaryAfter fragmentLeaf currentKey) (auxAccept (constantOne 1))
    (suc z) xs (certainZero xs rejected) step
  apply leafHeaderReject raw
  apply compositionRecover fragmentLeaf (fun _ : Fin 1 => currentKey) (suc z) xs ![raw] pick
  intro i
  obtain rfl := Fin.eq_zero i
  exact key

theorem exact_OpenCoverAuxFragmentLeaf : ExactOpenCoverAuxFragmentLeaf := by
  intro body α Γ prior actual noAux
  let R := auxSyntaxUpdate fragmentLeaf (constantOne 1)
  let Q := unary (header 2 2) z (suc prior)
  apply exact_OpenCoverSharedMemoRowCases R body α Γ prior (suc z) Q actual
  intro β j Δ old keep row
  have reject := renameInto noAux j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at reject
  simp only [Q,unaryRename,zRelabel,sucRelabel]
  exact atPhysicalRow (prior.relabel j) old reject row.update

#print axioms headerZeroOfNotOne
#print axioms exact_OpenCoverAuxFragmentLeaf

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentLeafProof
