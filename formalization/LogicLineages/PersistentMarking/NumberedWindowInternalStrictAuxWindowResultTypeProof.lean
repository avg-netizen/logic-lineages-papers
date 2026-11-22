module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport successorValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc sucNeZeroApply)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt certain)
open NumberedWindowInternalAuxWindowStepTargets (resultCode admittedChildren)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalStrictAuxWindowHeaderTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem typeAtStep (base : Program 2) (T : Program 1)
    (ctx ty dom cod fn arg old : OTerm α)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate base T) (suc ty) (memoPrior dom cod fn arg) old ctx))) :
    Nonempty (Derivation body Γ (eqn ty cod)) := by
  let prior := memoPrior dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey parent xs)) :=
    unaryGraph .succ (.projection 0) parent prior xs (successorValue ![prior]) (projectionValue 0 xs)
  obtain ⟨shape,read⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  have header := unaryGraph termShape currentKey (suc z) parent xs shape key
  have stored := unaryGraph (field 1) currentKey cod parent xs read.2.1 key
  have result : Nonempty (Derivation body Γ (programGraph resultCode (suc cod) xs)) :=
    unaryGraph .succ (childAt 1) (suc cod) cod xs (successorValue ![cod]) stored
  have positive := successorBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive T) (suc ty) z xs header step
  let G := conjunction certain (admittedChildren T)
  let P := programGraph G (suc z) xs
  apply formulaCases P _
  · have actual := successorBranchElim G (constantZero 4) resultCode (suc ty) z xs
      (show Nonempty (Derivation body (P :: Γ) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp positive P)
    obtain ⟨same⟩ := valueUnique resultCode (suc ty) (suc cod) xs actual (withHyp result P)
    exact ⟨cancelSuc same⟩
  · have rejected := conjunctionReject certain (admittedChildren T) xs
      (body := body) (Gamma := P.not :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have badZero := zeroBranchElim G (constantZero 4) resultCode (suc ty) xs rejected
      (withHyp positive P.not)
    obtain ⟨impossible⟩ := valueUnique (constantZero 4) (suc ty) z xs badZero (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

private theorem atUpdate (base : Program 2) (T : Program 1)
    (ctx ty dom cod fn arg old value : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx ty (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate base T) old (memoPrior dom cod fn arg) ctx)))
    (update : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate base T) value (memoPrior dom cod fn arg) old ctx))) :
    Nonempty (Derivation body Γ (eqn ty cod)) := by
  let R := strictAuxUpdate base T
  let F := selectedIntrinsic R
  let key := auxiliaryTerm dom cod fn arg
  let prior := memoPrior dom cod fn arg
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx ty key).mp parent
  have parentRow := (sameContext R (suc ty) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc ty) ![key,ctx,z] actual parentRow
  have atSameOutput := outputTransport R value (suc ty) ![prior,old,ctx,z] agree update
  exact typeAtStep base T ctx ty dom cod fn arg old atSameOutput

private theorem withTable (base : Program 2) (T : Program 1)
    (ctx ty dom cod fn arg old : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx ty (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate base T) old (memoPrior dom cod fn arg) ctx))) :
    Nonempty (Derivation body Γ (eqn ty cod)) := by
  let R := strictAuxUpdate base T
  apply programCases R ![memoPrior dom cod fn arg,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  rw [eqnRelabel]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate base T (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) (old.relabel j) value parent' table' update

theorem exact_OpenStrictAuxWindowResultType : ExactOpenStrictAuxWindowResultType := by
  intro base T body α Γ ctx ty dom cod fn arg parent
  let R := strictAuxUpdate base T
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  rw [eqnRelabel]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  exact withTable base T (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) old parent' table

#print axioms exact_OpenStrictAuxWindowResultType

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
