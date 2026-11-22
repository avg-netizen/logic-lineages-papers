module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph contextTable)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalCoverStrictAuxIntroduceRowProof (exact_OpenCoverStrictAuxIntroduceRow)
open NumberedWindowInternalCoverStrictAuxIntroduceTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem childrenRename (B : Program 2) (T : Program 1)
    (ctx dom cod fn arg : OTerm α) {β : Type} (j : α → β) :
    (strictAuxChildren B T ctx dom cod fn arg).relabel j =
      strictAuxChildren B T (ctx.relabel j) (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) := by
  simp only [strictAuxChildren,conjunctionRename,unaryRename,windowGraph,programRename,
    tripleInputsRename,sucRelabel,zRelabel,rawConsRename]

private theorem finishWithTable (B : Program 2) (T : Program 1) (ctx dom cod fn arg old : OTerm α)
    (child : Nonempty (Derivation body Γ (strictAuxChildren B T ctx dom cod fn arg)))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate B T) old (memoPrior dom cod fn arg) ctx))) :
    Nonempty (Derivation body Γ (windowGraph (strictAuxWindow B T) ctx cod (auxiliaryTerm dom cod fn arg))) := by
  let R := strictAuxUpdate B T
  let prior := memoPrior dom cod fn arg
  let raw := auxiliaryTerm dom cod fn arg
  have updated := exact_OpenCoverStrictAuxIntroduceRow B T body α Γ ctx dom cod fn arg old child table
  have row := exact_OpenContextMemoSuccessor R body α Γ (suc cod) prior old ctx table updated
  have value := (sameContext R (suc cod) ctx raw).mpr row
  exact (exact_OpenIntrinsicQuery (strictAuxIntrinsic B T) body α Γ ctx cod raw).mpr value

theorem exact_OpenCoverStrictAuxIntroduce : ExactOpenCoverStrictAuxIntroduce := by
  intro B T body α Γ ctx dom cod fn arg child
  let R := strictAuxUpdate B T
  let Q := windowGraph (strictAuxWindow B T) ctx cod (auxiliaryTerm dom cod fn arg)
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,ctx,z] Q
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  have actual := renameInto child j Δ keep
  rw [childrenRename] at actual
  simp only [Q,windowGraph,programRename,tripleInputsRename,auxiliaryRename,sucRelabel,zRelabel]
  exact finishWithTable B T (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) old actual table

#print axioms childrenRename
#print axioms exact_OpenCoverStrictAuxIntroduce

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
