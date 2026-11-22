module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalCoverHeadWindowTargets (headPrior headKey headArity)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α)) (j : α → β) :
    (headPrior b h tail).relabel j =
      headPrior b (h.relabel j) (tail.map (fun t => t.relabel j)) := by
  have pairRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [headPrior,pairRename,packedBodyRename,numeralRename,List.map_cons]

private theorem atStep (A : Program 2) (T : Program 1) (b : Bool) (ctx h result old : OTerm α)
    (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (actual : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate A T) (suc result) (headPrior b h tail) old ctx))) :
    Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,headKey b h tail])) := by
  let prior := headPrior b h tail
  let raw := headKey b h tail
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have shape := exact_OpenCoverHeadShape b body α Γ h tail len
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape.notAux key
  have picked := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive T) (suc result) xs noAux actual
  apply compositionRecover A ![.projection 2,currentKey] (suc result) xs ![ctx,raw] picked
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i

theorem selectedActualHeadBase (A : Program 2) (T : Program 1)
    (b : Bool) (ctx h result : OTerm α) (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (Q : Formula α)
    (actual : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (headKey b h tail))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (programGraph A (suc (result.relabel j))
          ![ctx.relabel j,headKey b (h.relabel j) (tail.map (fun t => t.relabel j))])) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := strictAuxUpdate A T
  apply exact_OpenSelectedFittedStepCases A T (headPrior b h tail) ctx result Q actual
  intro β j Δ old keep step
  let Fit : OTerm β → Prop := fun prior => Nonempty (Derivation body Δ
    (contextStep R (suc (result.relabel j)) prior old (ctx.relabel j)))
  have aligned : Fit (headPrior b (h.relabel j) (tail.map (fun t => t.relabel j))) :=
    Eq.mp (congrArg Fit (priorRename b h tail j)) step
  have len' : ((h.relabel j)::tail.map (fun t => t.relabel j)).length = headArity b := by
    simpa only [List.length_cons,List.length_map] using len
  exact next β j Δ keep (atStep A T b (ctx.relabel j) (h.relabel j) (result.relabel j) old _ len' aligned)

#print axioms selectedActualHeadBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowStepProof
