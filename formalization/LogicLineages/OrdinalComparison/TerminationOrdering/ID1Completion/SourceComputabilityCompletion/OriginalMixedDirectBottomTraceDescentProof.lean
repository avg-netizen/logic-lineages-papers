module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
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
open OriginalMixedDirectBottomTrace
open InternalQuotientComparisonProof (orLeft orRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem acceptingRunNonzero (source : Program 2) (leaf : Program 4) (out code state : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition source leaf) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
    Nonempty (Derivation body Delta (eqn state z).not) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hf⟩ := hf
  let P := eqn state z
  have hz := fixedValue (body := body) (Gamma := P :: Delta) (transition source leaf) z code
    ((OriginalMixedDirectBottomTraceProof.rejectZero source leaf body alpha (P :: Delta)).1)
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
  obtain ⟨hzf⟩ := valueUnique (finish source leaf) (suc z) z (Fin.cons z Fin.elim0) hfinish ((OriginalMixedDirectBottomTraceProof.rejectZero source leaf body alpha (P :: Delta)).2)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hzf)⟩

def second (g a : Program 1) : Program 1 :=
 InternalAcceptance.branch (normalize g) (InternalAcceptance.constantZero 1) a

theorem secondRecover (g a : Program 1) (state next : OTerm alpha)
 (hn : Nonempty (Derivation body Delta (eqn next z).not))
 (ht : Nonempty (Derivation body Delta (graph1 (second g a) next state))) :
 Nonempty (Derivation body Delta (graph1 g (suc z) state ⊓ graph1 a next state)) := by
 let P := graph1 g (suc z) state
 let Q := graph1 a next state
 obtain ⟨ht⟩ := ht
 obtain ⟨hn⟩ := hn
 have hy : Nonempty (Derivation body (P :: Delta) (P ⊓ Q)) := by
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact combine hp (successorBranchElim (normalize g) (InternalAcceptance.constantZero 1) a next z ![state]
   (normalizeAccept g ![state] hp) ⟨addHyp ht P⟩)
 have hno : Nonempty (Derivation body (P.not :: Delta) (P ⊓ Q)) := by
  have hz := zeroBranchElim (normalize g) (InternalAcceptance.constantZero 1) a next ![state]
   (normalizeReject g ![state] ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp ht P.not⟩
  obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 1) next z ![state] hz (constantZeroValue _)
  exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn P.not) he)⟩
 obtain ⟨hy⟩ := hy
 obtain ⟨hno⟩ := hno
 exact ⟨disjunctionElimination (excludedMiddle P) (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

def choice (g1 g2 a1 a2 : Program 1) : Program 1 :=
 InternalAcceptance.branch (normalize g1) (second g2 a2) a1

theorem choiceRecover (g1 g2 a1 a2 : Program 1) (state next : OTerm alpha)
 (hn : Nonempty (Derivation body Delta (eqn next z).not))
 (ht : Nonempty (Derivation body Delta (graph1 (choice g1 g2 a1 a2) next state))) :
 Nonempty (Derivation body Delta
  ((graph1 g1 (suc z) state ⊓ graph1 a1 next state) ⊔
   (graph1 g2 (suc z) state ⊓ graph1 a2 next state))) := by
 let P := graph1 g1 (suc z) state
 let R := (graph1 g1 (suc z) state ⊓ graph1 a1 next state) ⊔ (graph1 g2 (suc z) state ⊓ graph1 a2 next state)
 obtain ⟨ht⟩ := ht
 obtain ⟨hn⟩ := hn
 have hy : Nonempty (Derivation body (P :: Delta) R) := by
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := successorBranchElim (normalize g1) (second g2 a2) a1 next z ![state]
   (normalizeAccept g1 ![state] hp) ⟨addHyp ht P⟩
  obtain ⟨h⟩ := combine hp ha
  exact ⟨orLeft h⟩
 have hno : Nonempty (Derivation body (P.not :: Delta) R) := by
  have hs := zeroBranchElim (normalize g1) (second g2 a2) a1 next ![state]
   (normalizeReject g1 ![state] ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp ht P.not⟩
  obtain ⟨h⟩ := secondRecover g2 a2 state next ⟨addHyp hn P.not⟩ hs
  exact ⟨orRight h⟩
 obtain ⟨hy⟩ := hy
 obtain ⟨hno⟩ := hno
 exact ⟨disjunctionElimination (excludedMiddle P) (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

theorem actualFrontDescent : OriginalMixedDirectBottomTraceDescentTargets.ActualFrontDescent := by
 intro source leaf body alpha Delta code head tail state next out hc ht hr hf
 have htail := InternalRawListRepeatProof.frontConsForward (transition source leaf) code head tail out state next hc ht hr
 have hn := acceptingRunNonzero source leaf out tail next htail hf
 have hstate := acceptingRunNonzero source leaf out code state hr hf
 let active := choice (OriginalHereditaryLambda.atState (lambdaHop source leaf))
  (OriginalHereditaryLambda.atState (applicationHop source leaf))
  (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive)
  (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive)
 have ha : Nonempty (Derivation body Delta (graph1 active next state)) :=
  OriginalHereditaryLambdaChildControlProof.nonzeroBranchElim (.projection 0)
   (InternalAcceptance.constantZero 1) active next state ![state] (projectionValue 0 ![state]) hstate ht
 have hh := choiceRecover _ _ _ _ state next hn ha
 exact InternalApplicationStepPeelSupportProof.andIntro hh htail

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
