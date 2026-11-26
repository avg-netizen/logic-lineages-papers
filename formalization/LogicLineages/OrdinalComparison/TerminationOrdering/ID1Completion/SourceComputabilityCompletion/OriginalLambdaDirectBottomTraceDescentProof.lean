module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open InternalControlGraphChoiceProof (excludedMiddle)
open InternalGraphCompositionFunctionalityProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRawListRepeat InternalRawListRepeatProof
open OriginalHereditaryLambdaRepeatSupportProof
open OriginalHereditaryLambdaChildStateProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open OriginalLambdaDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem acceptingRunNonzero (source : Program 2) (leaf : Program 4) (out code state : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition source leaf) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
    Nonempty (Derivation body Delta (eqn state z).not) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hf⟩ := hf
  let P := eqn state z
  have hz := fixedValue (body := body) (Gamma := P :: Delta) (transition source leaf) z code
    ((OriginalLambdaDirectBottomTraceProof.rejectZero source leaf body alpha (P :: Delta)).1)
  have hstate : Nonempty (Derivation body (P :: Delta)
      (repeatGraph (transition source leaf) z code state)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 (P :: Delta)
      (OrdinaryArithmetic.graphFormula (repeatProgram (transition source leaf))) z
      (Fin.cons code (Fin.cons z Fin.elim0)) (Fin.cons code (Fin.cons state Fin.elim0)) _ hz
    intro i
    rw [InternalSourceInversionSupportProof.onEquality]
    exact Fin.cases ⟨refl code⟩ (Fin.cases
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (fun k => Fin.elim0 k)) i
  obtain ⟨he⟩ := valueUnique (repeatProgram (transition source leaf)) out z
    (Fin.cons code (Fin.cons state Fin.elim0)) ⟨addHyp hr P⟩ hstate
  have hfinish := headTransport (finish source leaf) (suc z) out z Fin.elim0 ⟨he⟩ ⟨addHyp hf P⟩
  obtain ⟨hzf⟩ := valueUnique (finish source leaf) (suc z) z (Fin.cons z Fin.elim0) hfinish ((OriginalLambdaDirectBottomTraceProof.rejectZero source leaf body alpha (P :: Delta)).2)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hzf)⟩

def activeBranch (source : Program 2) (leaf : Program 4) : Program 1 :=
 InternalAcceptance.branch (normalize (OriginalHereditaryLambda.atState (hop source leaf)))
  (InternalAcceptance.constantZero 1) (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive)
theorem activeBranchRecover (source : Program 2) (leaf : Program 4) (state next : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn next z).not))
    (ht : Nonempty (Derivation body Delta (graph1 (activeBranch source leaf) next state))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalHereditaryLambda.atState (hop source leaf)) (suc z) state ⊓
        graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state)) := by
  let P := graph1 (OriginalHereditaryLambda.atState (hop source leaf)) (suc z) state
  let Q := graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state
  obtain ⟨ht⟩ := ht
  obtain ⟨hn⟩ := hn
  have hy : Nonempty (Derivation body (P :: Delta) (P ⊓ Q)) := by
    have hp : Nonempty (Derivation body (P :: Delta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact combine hp (successorBranchElim (normalize (OriginalHereditaryLambda.atState (hop source leaf)))
      (InternalAcceptance.constantZero 1) (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next z (Fin.cons state Fin.elim0)
      (normalizeAccept (OriginalHereditaryLambda.atState (hop source leaf)) _ hp) ⟨addHyp ht _⟩)
  have hno : Nonempty (Derivation body (P.not :: Delta) (P ⊓ Q)) := by
    have hz := zeroBranchElim (normalize (OriginalHereditaryLambda.atState (hop source leaf)))
      (InternalAcceptance.constantZero 1) (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next (Fin.cons state Fin.elim0)
      (normalizeReject (OriginalHereditaryLambda.atState (hop source leaf)) _
        ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp ht _⟩
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 1) next z
      (Fin.cons state Fin.elim0) hz (constantZeroValue _)
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn _) he)⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

theorem actualFrontDescent : OriginalLambdaDirectBottomTraceDescentTargets.ActualFrontDescent := by
 intro source leaf body alpha Delta s t cert parameter code head tail state next out hp hl hc ht hr hf
 have htail := InternalRawListRepeatProof.frontConsForward (transition source leaf)
  code head tail out state next hc ht hr
 have hn := acceptingRunNonzero source leaf out tail next htail hf
 have hstate := OriginalHereditaryLambdaChildControlProof.liveNonzero state s t cert parameter hl
 have hab : Nonempty (Derivation body Delta (graph1 (activeBranch source leaf) next state)) :=
  OriginalHereditaryLambdaChildControlProof.nonzeroBranchElim (.projection 0)
   (InternalAcceptance.constantZero 1) (activeBranch source leaf) next state (Fin.cons state Fin.elim0)
   (projectionValue 0 (Fin.cons state Fin.elim0)) hstate ht
 have h := activeBranchRecover source leaf state next hn hab
 have hg := atLiveRecover (hop source leaf) (suc z) state s t cert parameter hl (projectLeft h)
 have hchild := atLiveRecover OriginalHereditaryLambda.childLive next state s t cert parameter hl (projectRight h)
 exact InternalApplicationStepPeelSupportProof.andIntro hg
  (InternalApplicationStepPeelSupportProof.andIntro hchild htail)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
