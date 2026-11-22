module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureDispatchProof
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
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSupportProof (trans addZero addSucc congSuc)
open NumberedWindowInternalSparsePathEnvelope (field)
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
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverSharedRecursionTargets (lambdaDispatch sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverNamedLeafMeasureDispatchProof (exact_OpenCoverNamedLeafMeasureDispatch)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (leafMeasureBase leafPair10)
open NumberedWindowInternalCoverNamedLeafMeasureTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (b : Bool) (ty i : OTerm α) (j : α → β) :
    (namedPrior b ty i).relabel j = namedPrior b (ty.relabel j) (i.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [namedPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem selfWeak (i : OTerm α) : Nonempty (Derivation body Γ (ltF i (suc i))) := by
  apply actualOriginalOrderIntroduction body α Γ i (suc i) z
  rw [onEquality]
  exact ⟨trans (addSucc i z) (congSuc (addZero i))⟩

private theorem fromBase (b : Bool) (M : Program 1) (ty i old p : OTerm α)
    (reports : let raw := namedTerm b.toNat ty i
      let xs : Fin 4 → OTerm α := ![namedPrior b ty i,old,z,z]
      Nonempty (Derivation body Γ (programGraph lambdaDispatch z xs)) ∧
      Nonempty (Derivation body Γ (programGraph certain z xs)) ∧
      Nonempty (Derivation body Γ (unary (header 3 1) z raw)) ∧
      Nonempty (Derivation body Γ (unary (header b.toNat 2) (suc z) raw)) ∧
      Nonempty (Derivation body Γ (unary (field 1) i raw)) ∧
      (b = true → Nonempty (Derivation body Γ (unary (header 0 2) z raw))))
    (actual : Nonempty (Derivation body Γ
      (unary (leafMeasureBase (namedMeasureBase M)) p (namedTerm b.toNat ty i)))) :
    Nonempty (Derivation body Γ (codePair p (suc z) i)) := by
  let raw := namedTerm b.toNat ty i
  have named := zeroBranchElim (header 3 1) (namedMeasureBase M) leafPair10
    p ![raw] reports.2.2.1 actual
  have pairReport : Nonempty (Derivation body Γ (unary namedMeasurePair p raw)) := by
    cases b
    · exact successorBranchElim (header 0 2) (branch (header 1 2) M namedMeasurePair)
        namedMeasurePair p z ![raw] reports.2.2.2.1 named
    · have bound := zeroBranchElim (header 0 2) (branch (header 1 2) M namedMeasurePair)
        namedMeasurePair p ![raw] (reports.2.2.2.2.2 rfl) named
      exact successorBranchElim (header 1 2) M namedMeasurePair p z ![raw] reports.2.2.2.1 bound
  apply compositionRecover pairing ![literal 1 1,field 1] p ![raw] ![suc z,i] pairReport
  intro j
  exact Fin.cases (literalGraph 1 ![raw]) (Fin.cases reports.2.2.2.2.1 (fun l => Fin.elim0 l)) j

private theorem fromRow (b : Bool) (M : Program 1) (ty i old p : OTerm α)
    (row : ObservedStep (sharedMeasureUpdate (leafMeasureBase (namedMeasureBase M)))
      body Γ (namedPrior b ty i) old p) :
    Nonempty (Derivation body Γ (codePair p (suc z) i)) := by
  let B := leafMeasureBase (namedMeasureBase M)
  let raw := namedTerm b.toNat ty i
  let prior := namedPrior b ty i
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have reports := exact_OpenCoverNamedLeafMeasureDispatch b body α Γ ty i old
  have aux := zeroBranchElim lambdaDispatch (measureUpdate B chosenCombine) (lambdaMeasureUpdate B)
    p xs reports.1 row.update
  have base := zeroBranchElim certain (unaryAfter B currentKey)
    (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p xs reports.2.1 aux
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have actual : Nonempty (Derivation body Γ (unary B p raw)) := by
    apply compositionRecover B (fun _ : Fin 1 => currentKey) p xs ![raw] base
    intro j
    obtain rfl := Fin.eq_zero j
    exact key
  exact fromBase b M ty i old p reports actual

theorem exact_OpenCoverNamedLeafSharedMeasure : ExactOpenCoverNamedLeafSharedMeasure := by
  intro b M body α Γ ty i p actual
  refine ⟨?_,selfWeak i⟩
  apply exact_OpenCoverSharedMemoRowCases (sharedMeasureUpdate (leafMeasureBase (namedMeasureBase M)))
    body α Γ (namedPrior b ty i) p _ actual
  intro β j Δ old keep row
  simp only [pairRename,sucRelabel,zRelabel]
  rw [priorRename] at row
  exact fromRow b M (ty.relabel j) (i.relabel j) old (p.relabel j) row

#print axioms exact_OpenCoverNamedLeafSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
