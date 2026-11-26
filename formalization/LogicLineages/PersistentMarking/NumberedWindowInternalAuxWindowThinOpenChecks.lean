module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureOpenDataProof (priorKey)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowThinTableProof (exact_OpenContextMemoSuccessor)
open NumberedWindowInternalAuxWindowThinOpenNodeProof (nodeValue)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem keyRename {β : Type} (dom cod fn arg : OTerm α) (j : α → β) :
    (priorKey dom cod fn arg).relabel j =
      priorKey (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) :=
  priorRename dom cod fn arg j

private theorem derive (base : Program 2) (T : Program 1) (ctx dom cod fn arg : OTerm α)
    (domOK : Nonempty (Derivation body Γ (unary T (suc z) dom)))
    (codOK : Nonempty (Derivation body Γ (unary T (suc z) cod)))
    (fnValue : Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc (rawCons dom cod)) ctx fn)))
    (argValue : Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc dom) ctx arg))) :
    Nonempty (Derivation body Γ (intrinsicGraph (selectedIntrinsic (windowUpdate base T))
      (suc cod) ctx (auxiliaryTerm dom cod fn arg))) := by
  let R := windowUpdate base T
  apply programCases (scratchTable (constantZero 2) R) ![priorKey dom cod fn arg,ctx,z] _
  intro β j Δ old hJ table
  simp only [intrinsicGraph,programRename,binaryInputsRename,auxiliaryRename,sucRelabel]
  simp only [tripleInputsRename,zRelabel,keyRename] at table
  have d := renameInto domOK j Δ hJ
  have c := renameInto codOK j Δ hJ
  have f := renameInto fnValue j Δ hJ
  have a := renameInto argValue j Δ hJ
  simp only [unaryRename,sucRelabel,zRelabel] at d c
  simp only [intrinsicGraph,programRename,binaryInputsRename,sucRelabel,rawConsRename] at f a
  exact nodeValue base T (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    old table d c f a

theorem exact_OpenAuxWindow : ExactOpenAuxWindow := by
  intro base T body α Γ ctx dom cod fn arg
  let F := selectedIntrinsic (windowUpdate base T)
  let W := intrinsicQuery F
  let premise := (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (windowGraph W ctx (rawCons dom cod) fn ⊓ windowGraph W ctx dom arg)
  let Δ := premise :: Γ
  have whole : Derivation body Δ premise := Derivation.hypothesis List.mem_cons_self
  have guards := Derivation.conjunctionLeft whole
  have children := Derivation.conjunctionRight whole
  have fnValue := (exact_OpenIntrinsicQuery F body α Δ ctx (rawCons dom cod) fn).mp
    ⟨Derivation.conjunctionLeft children⟩
  have argValue := (exact_OpenIntrinsicQuery F body α Δ ctx dom arg).mp
    ⟨Derivation.conjunctionRight children⟩
  have parent := derive base T ctx dom cod fn arg ⟨Derivation.conjunctionLeft guards⟩
    ⟨Derivation.conjunctionRight guards⟩ fnValue argValue
  obtain ⟨out⟩ := (exact_OpenIntrinsicQuery F body α Δ ctx cod (auxiliaryTerm dom cod fn arg)).mpr parent
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenIntrinsicQuery
#print axioms exact_OpenContextMemoSuccessor
#print axioms exact_OpenAuxWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenChecks
