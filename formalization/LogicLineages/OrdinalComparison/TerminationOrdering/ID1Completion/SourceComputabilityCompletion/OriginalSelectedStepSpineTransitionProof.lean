module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ClaudeSupervisedCompletion.InverseGuardCandidate
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationResultStack (liftP)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalSelectedStepSpineStateProof OriginalSelectedStepSpineRepeatSyntaxProof
open OriginalSelectedCheckerInverseGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reverse a single ORIGINAL accepted peel. The inverse guard supplies both
actual application graphs, and the child guard lifts across their common
argument without changing raw endpoints, certificate or parameter. -/
theorem acceptedAtEdge (endpoint : Program 6) (state out s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hg : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) (suc z) state parameter)))
    (ht : Nonempty (Derivation body Gamma (transitionGraph endpoint out state parameter)))
    (ho : Nonempty (Derivation body Gamma (stateGuard out parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) := by
  apply acceptedGuardCases endpoint state s t k parameter _ he hg
  intro beta j Delta hj d e arrow f g a childK child hw
  rw [stateGuardRename]
  have ht' := renameInto ht j Delta hj
  rw [transitionGraphRename] at ht'
  have ho' := renameInto ho j Delta hj
  rw [stateGuardRename] at ho'
  have he' := renameInto he j Delta hj
  rw [graph3Rename] at he'
  have hc := andLeft (andRight hw)
  have heq := valueUnique (transitionP endpoint) (out.relabel j) child
    (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) ht'
    (andRight (andRight hw))
  have hchild := headTransport stateTest (suc z) (out.relabel j) child
    (Fin.cons (parameter.relabel j) Fin.elim0) heq ho'
  have hlift := OriginalSelectedStepSpineApplicationProof.rawLift endpoint d e arrow f g a childK
    (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) (andLeft hw)
    (stateRecover child f g childK (parameter.relabel j) hc hchild)
  exact stateValue (state.relabel j) (s.relabel j) (t.relabel j) (k.relabel j)
    (parameter.relabel j) he' hlift

/-- Rejected original guards leave the state literally fixed; accepted
guards use their recovered typed raw application layer. -/
theorem atEdge (endpoint : Program 6) (state out s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (ht : Nonempty (Derivation body Gamma (transitionGraph endpoint out state parameter)))
    (ho : Nonempty (Derivation body Gamma (stateGuard out parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) := by
  let G := graph2 (guardP endpoint) (suc z) state parameter
  apply formulaCases G (stateGuard state parameter)
  · exact acceptedAtEdge endpoint state out s t k parameter (withHyp he G)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht G) (withHyp ho G)
  · have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
      (body := body) (Gamma := G.not :: Gamma)
      (liftP InternalApplicationStepPeel.structuralGuard) (endpointAtP endpoint)
      (Fin.cons state (Fin.cons parameter Fin.elim0))
      (show Nonempty (Derivation body (G.not :: Gamma) G.not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have heq := valueUnique (transitionP endpoint) out state
      (Fin.cons state (Fin.cons parameter Fin.elim0)) (withHyp ht G.not)
      (rejectedTransition endpoint state parameter hz)
    exact headTransport stateTest (suc z) out state (Fin.cons parameter Fin.elim0)
      heq (withHyp ho G.not)

/-- Bind all original edge selectors internally. Every raw state and every
endpoint Program is covered, independently of decoding and calibration. -/
theorem atState (endpoint : Program 6) (state out parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (transitionGraph endpoint out state parameter)))
    (ho : Nonempty (Derivation body Gamma (stateGuard out parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) := by
  apply queryCases (![source,target,step] : Fin 3 → Program 1) (Fin.cons state Fin.elim0) _
  intro beta j ys Delta hj hq
  rw [stateGuardRename]
  simp only [consTermRename,emptyRename] at hq
  have ht' := renameInto ht j Delta hj
  rw [transitionGraphRename] at ht'
  have ho' := renameInto ho j Delta hj
  rw [stateGuardRename] at ho'
  exact atEdge endpoint (state.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2)
    (parameter.relabel j)
    (edgeReconstruction (state.relabel j) (ys 0) (ys 1) (ys 2)
      (andIntro (hq 0) (andIntro (hq 1) (hq 2)))) ht' ho'

theorem transitionBackward (endpoint : Program 6) :
    BackwardStep (transitionP endpoint) stateTest := by
  intro body alpha Gamma state out parameter ht ho
  exact atState endpoint state out parameter ht ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTransitionProof
