module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureDispatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalPairing (pairing)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate certain measureAt)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasureUpdate)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverSharedRecursionTargets (lambdaDispatch sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverTypeLeafMeasureDispatchProof (exact_OpenCoverTypeLeafMeasureDispatch)
open NumberedWindowInternalCoverTypeLeafMeasureTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty : OTerm α) (j : α → β) :
    (typeLeafPrior ty).relabel j = typeLeafPrior (ty.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [typeLeafPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem fromRow (M : Program 1) (ty old p : OTerm α)
    (row : ObservedStep (sharedMeasureUpdate (leafMeasureBase M)) body Γ (typeLeafPrior ty) old p) :
    Nonempty (Derivation body Γ (codePair p (suc z) z)) := by
  let B := leafMeasureBase M
  let raw := typeLeafTerm ty
  let prior := typeLeafPrior ty
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have branches := exact_OpenCoverTypeLeafMeasureDispatch body α Γ ty old
  have aux := zeroBranchElim lambdaDispatch (measureUpdate B chosenCombine) (lambdaMeasureUpdate B)
    p xs branches.1 row.update
  have base := zeroBranchElim certain (unaryAfter B currentKey)
    (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p xs branches.2.1 aux
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have actual : Nonempty (Derivation body Γ (unary B p raw)) := by
    apply compositionRecover B (fun _ : Fin 1 => currentKey) p xs ![raw] base
    intro i
    obtain rfl := Fin.eq_zero i
    exact key
  have pairingCode := successorBranchElim (header 3 1) M leafPair10 p z ![raw] branches.2.2 actual
  apply compositionRecover pairing ![literal 1 1,constantZero 1] p ![raw] ![suc z,z] pairingCode
  intro i
  exact Fin.cases (literalGraph 1 ![raw]) (Fin.cases (constantZeroValue ![raw]) (fun j => Fin.elim0 j)) i

theorem exact_OpenCoverTypeLeafSharedMeasure : ExactOpenCoverTypeLeafSharedMeasure := by
  intro M body α Γ ty p actual
  apply exact_OpenCoverSharedMemoRowCases (sharedMeasureUpdate (leafMeasureBase M))
    body α Γ (typeLeafPrior ty) p _ actual
  intro β j Δ old keep row
  simp only [pairRename,sucRelabel,zRelabel]
  rw [priorRename] at row
  exact fromRow M (ty.relabel j) old (p.relabel j) row

#print axioms exact_OpenCoverTypeLeafSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
