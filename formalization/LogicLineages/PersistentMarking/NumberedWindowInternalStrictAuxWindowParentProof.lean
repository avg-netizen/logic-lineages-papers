module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowOpenProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalStrictAuxWindowOpenProof (exact_OpenStrictAuxWindowRow)
open NumberedWindowInternalStrictAuxWindowParentTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem childrenRename (base : Program 2) (T : Program 1)
    (ctx dom cod fn arg : OTerm α) {β : Type} (j : α → β) :
    (strictAuxChildren base T ctx dom cod fn arg).relabel j =
      strictAuxChildren base T (ctx.relabel j) (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) := by
  simp only [strictAuxChildren,conjunctionRename,unaryRename,windowGraph,programRename,
    tripleInputsRename,sucRelabel,zRelabel,rawConsRename]

private theorem atUpdate (base : Program 2) (T : Program 1)
    (ctx dom cod fn arg old value : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx cod (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate base T) old (memoPrior dom cod fn arg) ctx)))
    (update : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate base T) value (memoPrior dom cod fn arg) old ctx))) :
    Nonempty (Derivation body Γ (strictAuxChildren base T ctx dom cod fn arg)) := by
  let R := strictAuxUpdate base T
  let F := selectedIntrinsic R
  let key := auxiliaryTerm dom cod fn arg
  let prior := memoPrior dom cod fn arg
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx cod key).mp parent
  have parentRow := (sameContext R (suc cod) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc cod) ![key,ctx,z] actual parentRow
  have atSameOutput := outputTransport R value (suc cod) ![prior,old,ctx,z] agree update
  exact exact_OpenStrictAuxWindowRow base T body α Γ ctx dom cod fn arg old table atSameOutput

private theorem withTable (base : Program 2) (T : Program 1)
    (ctx dom cod fn arg old : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx cod (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate base T) old (memoPrior dom cod fn arg) ctx))) :
    Nonempty (Derivation body Γ (strictAuxChildren base T ctx dom cod fn arg)) := by
  let R := strictAuxUpdate base T
  apply programCases R ![memoPrior dom cod fn arg,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  rw [childrenRename]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate base T (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) (old.relabel j) value parent' table' update

theorem exact_OpenStrictAuxWindowParent : ExactOpenStrictAuxWindowParent := by
  intro base T body α Γ ctx dom cod fn arg parent
  let R := strictAuxUpdate base T
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  rw [childrenRename]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  exact withTable base T (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) old parent' table

#print axioms exact_OpenStrictAuxWindowParent

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
