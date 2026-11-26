module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoClampProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureArgumentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredOrdinaryListProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (measurePair)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (renameRow)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey OrdinaryOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof (exact_OpenSelectedGrammarOrdinaryScratch)
open NumberedWindowInternalCoverOrdinaryMeasureCutProof (exact_OpenCoverOrdinaryMeasureCut)
open NumberedWindowInternalCoverOrdinaryMeasureArgumentProof (exact_OpenOrdinaryBumpFromArgument)
open NumberedWindowInternalCoverLambdaMeasureRowBumpProof (exact_OpenCoverLambdaBumpPair)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets (ArgumentHit)
open NumberedWindowInternalCoverArgumentMemoClampProof (exact_OpenCoverArgumentMemoClamp)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (consumeArgument)
open NumberedWindowInternalCoverGuardedOrdinaryListTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selfWeak (x : OTerm α) : Nonempty (Derivation body Γ (ltF x (suc x))) := by
  apply actualOriginalOrderIntroduction body α Γ x (suc x) z
  rw [onEquality]
  exact ⟨trans (addSucc x z) (congSuc (addZero x))⟩

private theorem atMeasured (V TV M F : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (h a p vertices ctx result ma d w st ts ars : OTerm α)
    (row : ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (ordinaryKey h a) p vertices ctx result)
    (arg : Nonempty (Derivation body Γ (unary (argumentMeasure F) ma a)))
    (pair : Nonempty (Derivation body Γ (codePair ma d w)))
    (hit : ArgumentHit s body Γ d w st ts ars a) :
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a))) := by
  let A := argumentMeasure F
  let P := lexicalFittedPrograms s V TV M A B T
  let L := lambdaLexicalBase s B T
  let R := selectedMeasure P.R
  have head := exact_OpenCoverHeadFittedWindow false s (numberedTypeBase s L) T
    body α Γ ctx h result [a] rfl row.typed
  have argument := exact_OpenCoverArgumentMemoClamp F body α Γ a ma arg
  have cut := exact_OpenCoverOrdinaryMeasureCut (numberedMeasureBase M A) A body α Γ h a p row.parent.measured
  have bump := exact_OpenOrdinaryBumpFromArgument A h a p ma cut argument
  have pp := exact_OpenCoverLambdaBumpPair body α Γ p ma d w pair bump
  have input : OrdinaryOwnInputs P.V R s body Γ p d w d w st ts ars h a :=
    ⟨hit.scope,hit.hit,selfWeak d,selfWeak w,head,row.parent.valid,row.parent.measured,pp⟩
  exact exact_OpenSelectedGrammarOrdinaryScratch P.V R s body α Γ p d w d w st ts ars vertices
    h a input row.parent.held

theorem exact_OpenCoverMeasuredOrdinaryListScratch : ExactOpenCoverMeasuredOrdinaryListScratch := by
  intro V TV M F B T s body α Γ h a p vertices ctx result actual args
  let P := lexicalFittedPrograms s V TV M (argumentMeasure F) B T
  apply consumeArgument F s a (memberGraph vertices (ordinaryKey h a)) args
  intro β j Δ ma d w st ts ars keep arg pair hit
  have row := renameRow P s j keep actual
  rw [ordinaryRename] at row
  rw [graphRename,ordinaryRename]
  exact atMeasured V TV M F B T s (h.relabel j) (a.relabel j) (p.relabel j) (vertices.relabel j)
    (ctx.relabel j) (result.relabel j) ma d w st ts ars row arg pair hit

#print axioms exact_OpenCoverMeasuredOrdinaryListScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredOrdinaryListProof
