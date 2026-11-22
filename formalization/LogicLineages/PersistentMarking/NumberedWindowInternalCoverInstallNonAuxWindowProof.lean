module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem installWithTable (A : Program 2) (T : Program 1) (ctx prior result old : OTerm α)
    (shape : Nonempty (Derivation body Γ (unary termShape z (suc prior))))
    (actual : Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,suc prior])))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate A T) old prior ctx))) :
    Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))) := by
  let R := strictAuxUpdate A T
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape key
  have branch := binaryGraph A (.projection 2) currentKey (suc result) ctx raw xs actual
    (projectionValue 2 xs) key
  have update : Nonempty (Derivation body Γ (contextStep R (suc result) prior old ctx)) :=
    zeroBranchIntro shapeCheck (binaryAfter A (.projection 2) currentKey) (strictAuxPositive T)
      (suc result) xs noAux branch
  have row := exact_OpenContextMemoSuccessor R body α Γ (suc result) prior old ctx table update
  have selected := (sameContext R (suc result) ctx raw).mpr row
  exact (exact_OpenIntrinsicQuery (strictAuxIntrinsic A T) body α Γ ctx result raw).mpr selected

theorem exact_OpenCoverInstallNonAuxWindow : ExactOpenCoverInstallNonAuxWindow := by
  intro A T body α Γ ctx prior result shape actual
  let R := strictAuxUpdate A T
  let Q := windowGraph (strictAuxWindow A T) ctx result (suc prior)
  apply programCases (scratchTable (constantZero 2) R) ![prior,ctx,z] Q
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  have shape' := renameInto shape j Δ keep
  have actual' := renameInto actual j Δ keep
  simp only [unaryRename,zRelabel,sucRelabel] at shape'
  simp only [programRename,binaryInputsRename,sucRelabel] at actual'
  simp only [Q,windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact installWithTable A T (ctx.relabel j) (prior.relabel j) (result.relabel j) old shape' actual' table

#print axioms exact_OpenCoverInstallNonAuxWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
