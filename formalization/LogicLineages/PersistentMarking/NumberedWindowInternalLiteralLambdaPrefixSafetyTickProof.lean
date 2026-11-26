module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyTickProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (emitState stateFrame)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem branchSafe {n : Nat} (test no yes : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (call : D B Γ (programGraph (branch test no yes) out xs))
    (left : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph no (out.relabel j) (fun i => (xs i).relabel j)) → D B Δ (prefixSafe (out.relabel j)))
    (right : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph yes (out.relabel j) (fun i => (xs i).relabel j)) → D B Δ (prefixSafe (out.relabel j))) :
    D B Γ (prefixSafe out) := by
  apply optionGraphCases test xs _
  · intro β j Δ keep zero
    rw [prefixSafeRename]
    have got := renameInto call j Δ keep
    rw [programRename] at got
    exact left β j Δ keep (zeroBranchElim test no yes (out.relabel j) _ zero got)
  · intro β j Δ k keep nonzero
    rw [prefixSafeRename]
    have got := renameInto call j Δ keep
    rw [programRename] at got
    exact right β j Δ keep (successorBranchElim test no yes (out.relabel j) k _ nonzero got)

private theorem emittingOne {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (call : D B Γ (programGraph (emitState (constantOne n) p) out xs)) :
    D B Γ (prefixSafe out) := by
  apply programCases p xs _
  intro β j Δ frame keep computed
  rw [prefixSafeRename]
  let ys : Fin n → OTerm β := fun i => (xs i).relabel j
  let st := stateTerm (suc z) frame
  have expected : D B Δ (programGraph (emitState (constantOne n) p) st ys) :=
    emitGraph _ _ (suc z) frame ys (oneConstantValue ys) computed
  have actual := renameInto call j Δ keep
  rw [programRename] at actual
  exact prefixSafeMove st (out.relabel j) (oneStateSafe st (headRead (suc z) frame))
    (valueUnique (emitState (constantOne n) p) st (out.relabel j) ys expected actual)

theorem exact_OpenPrefixLiveSafe (W : Program 3) (out : OTerm α) (xs : Fin 5 → OTerm α)
    (h : D B Γ (programGraph (prefixLive W) out xs)) :
    D B Γ (prefixSafe out) := by
  apply branchSafe isLambdaPrefix prefixAccept
    (branch (prefixValidation W) prefixReject (emitState (constantOne 5) prefixNext)) out xs h
  · intro β j Δ _ one
    exact emittingOne (constantZero 5) (out.relabel j) _ one
  · intro β j Δ _ called
    apply branchSafe (prefixValidation W) prefixReject (emitState (constantOne 5) prefixNext) (out.relabel j) _ called
    · intro γ k Θ _ rejected
      let ys : Fin 5 → OTerm γ := fun i => ((xs i).relabel j).relabel k
      have expected : D B Θ (programGraph prefixReject rejectedState ys) :=
        emitGraph _ _ z z ys (constantZeroValue ys) (constantZeroValue ys)
      exact rejectedStateSafe ((out.relabel j).relabel k)
        (valueUnique prefixReject ((out.relabel j).relabel k) rejectedState ys rejected expected)
    · intro γ k Θ _ new
      exact emittingOne prefixNext ((out.relabel j).relabel k) _ new

theorem exact_OpenPrefixTickSafe (W : Program 3) (before out : OTerm α)
    (safe : D B Γ (prefixSafe before))
    (tick : D B Γ (programGraph (prefixTick W) out ![before])) :
    D B Γ (prefixSafe out) := by
  apply branchSafe stateFrame (.projection 0) (prefixPerform W) out ![before] tick
  · intro β j Δ keep old
    rw [inputsRename] at old
    have same := valueUnique (.projection 0) (before.relabel j) (out.relabel j)
      ![before.relabel j] (projectionValue 0 ![before.relabel j]) old
    have input := renameInto safe j Δ keep
    rw [prefixSafeRename] at input
    exact prefixSafeMove (before.relabel j) (out.relabel j) input same
  · intro β j Δ _ live
    rw [inputsRename] at live
    apply programCompositionCases (prefixLive W)
      ![prefixReadSlot 0,prefixReadSlot 1,prefixReadSlot 2,prefixReadSlot 3,prefixReadSlot 4]
      (out.relabel j) ![before.relabel j] _ live
    intro γ k values Θ _ input _
    rw [prefixSafeRename]
    exact exact_OpenPrefixLiveSafe W ((out.relabel j).relabel k) values input

#print axioms exact_OpenPrefixLiveSafe
#print axioms exact_OpenPrefixTickSafe
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyTickProof
