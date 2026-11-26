module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenParentsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredParentsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureOpenThinEvaluationProof (deriveValue)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets (accepted)
open NumberedWindowInternalMeasuredExchangeThinOpenComposeProof (grammarTape putCover composeParents)
open NumberedWindowInternalMeasuredExchangeThinOpenParentsProof
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalLiteralBiAuxRawMemoOpenProof (biAuxRawMemo)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def biAuxMeasuredExchange (s : Settings) (X : Program 2) (V baseM : Program 1) (P : Program 2) (G : Program 3) :
    Program 2 :=
  let M := selectedMeasure (measureUpdate baseM P)
  guardedExchange (factoredCover V M G) s (pairedExchange (measuredExchange M (biAuxRawMemo X V)))

private theorem coverOfSharedMeasure (V M : Program 1) (X : Program 2) (G : Program 3) (s : Settings)
    (q r m : OTerm α) (original : ParentReports V X B Γ q r)
    (left : D B Γ (unary M m q)) (right : D B Γ (unary M m r)) :
    D B Γ (accepted (guardedExchange (factoredCover V M G) s (pairedExchange (measuredExchange M X))) q r) := by
  apply programCases G (grammarTape s m) _
  intro β j Δ produced keep report
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel]
  simp only [grammarTape,tripleInputsRename,numeralRename] at report
  have opened := renameReports original j Δ keep
  have a := renameUnary M m q j Δ keep left
  have b := renameUnary M m r j Δ keep right
  let u := q.relabel j
  let v := r.relabel j
  let n := m.relabel j
  have c := putCover V M G s produced u n opened.syntaxA a report
  have d := putCover V M G s produced v n opened.syntaxB b report
  exact composeParents M X (factoredCover V M G) s u v n produced opened.forward opened.backward a b c d

/-- Both parent cover callbacks see the same *actual* computed child
measure pair, no matter which operand was moved. This ties the cover
agreement to the original opened and untyped exchange graphs. -/
theorem exact_OpenMeasuredBiAuxParent (s : Settings) (X : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (dom cod f g a b mf ma : OTerm α)
    (raw : ParentReports V (biAuxRawMemo X V) B Γ (auxiliaryTerm dom cod f a) (auxiliaryTerm dom cod g b))
    (fM : D B Γ (measureGraph baseM P mf f)) (gM : D B Γ (measureGraph baseM P mf g))
    (aM : D B Γ (measureGraph baseM P ma a)) (bM : D B Γ (measureGraph baseM P ma b)) :
    D B Γ (accepted (biAuxMeasuredExchange s X V baseM P G)
      (auxiliaryTerm dom cod f a) (auxiliaryTerm dom cod g b)) := by
  let M := selectedMeasure (measureUpdate baseM P)
  apply programCases P ![mf,ma] _
  intro β j Δ combined keep measured
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,auxiliaryRename]
  rw [binaryInputsRename] at measured
  have opened := renameReports raw j Δ keep
  simp only [auxiliaryRename] at opened
  have f' := renameUnary M mf f j Δ keep fM
  have g' := renameUnary M mf g j Δ keep gM
  have a' := renameUnary M ma a j Δ keep aM
  have b' := renameUnary M ma b j Δ keep bM
  let d := dom.relabel j
  let c := cod.relabel j
  let vf := mf.relabel j
  let va := ma.relabel j
  have lf := deriveValue baseM P d c (f.relabel j) (a.relabel j) vf va combined f' a' measured
  have rg := deriveValue baseM P d c (g.relabel j) (b.relabel j) vf va combined g' b' measured
  exact coverOfSharedMeasure V M (biAuxRawMemo X V) G s _ _ combined opened lf rg

#print axioms exact_OpenMeasuredBiAuxParent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredParentsProof
