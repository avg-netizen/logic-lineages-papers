module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverWrapperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalParameterizedBoundedDescentNormalizer
open InternalParameterizedBoundedDescentNormalizerStepSupportProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalIndexedObserverRangeSyntaxProof (rangeRename)
open OriginalClassContextAllPositionSelectionOutputProof (middleTransport)
open OriginalIndexedObserverWrapperProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem identityObserver (observer : Program 3)
    (mark cutoff input parameter : InternalGraphComposition.OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph3 observer mark cutoff input parameter).iff (graph3 observer mark cutoff input parameter))) := by
  have h : Derivation body Delta ((graph3 observer mark cutoff input parameter).imp
      (graph3 observer mark cutoff input parameter)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction h h⟩

theorem replaceOutput (observer : Program 3)
    (mark cutoff out candidate input parameter : InternalGraphComposition.OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out candidate)))
    (hi : Nonempty (Derivation body Delta
      ((graph3 observer mark cutoff candidate parameter).iff (graph3 observer mark cutoff input parameter)))) :
    Nonempty (Derivation body Delta
      ((graph3 observer mark cutoff out parameter).iff (graph3 observer mark cutoff input parameter))) := by
  let A := graph3 observer mark cutoff out parameter
  obtain ⟨hc⟩ := middleTransport observer mark cutoff out candidate parameter (withHyp he A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hi'⟩ := withHyp hi A
  have hf := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hi') hc)
  let B := graph3 observer mark cutoff input parameter
  obtain ⟨hi''⟩ := withHyp hi B
  have hcandidate : Nonempty (Derivation body (B :: Delta)
      (graph3 observer mark cutoff candidate parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi'')
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨he''⟩ := withHyp he B
  obtain ⟨hb⟩ := middleTransport observer mark cutoff candidate out parameter ⟨symm he''⟩ hcandidate
  exact ⟨Derivation.conjunctionIntroduction hf (Derivation.implicationIntroduction hb)⟩

/-- The literal original transition returns its representative candidate or
its unchanged input. Index, context parameter and actual range stay fixed. -/
theorem transitionPreservation (condition R V : Program 2) (observer : Program 3)
    (hR : Keeps condition R observer) :
    Keeps condition (transition R V) observer := by
  intro body alpha Delta out input parameter mark cutoff hRange ha ht
  change Nonempty (Derivation body Delta
    ((graph3 observer mark cutoff out parameter).iff (graph3 observer mark cutoff input parameter)))
  change Nonempty (Derivation body Delta (graph2 condition InternalOriginalStepGuard.one input parameter)) at ha
  change Nonempty (Derivation body Delta (graph2 (transition R V) out input parameter)) at ht
  apply programCases R (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta candidate hj hr
  simp only [iffRename,graph3Rename]
  have hr' : Nonempty (Derivation body Theta
      (graph2 R candidate (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hr
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ha'
  have ht' := renameInto ht j Theta hj
  rw [graph2Rename] at ht'
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  let xs : Fin 2 → InternalGraphComposition.OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let ys : Fin 3 → InternalGraphComposition.OTerm beta := Fin.cons candidate
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have hc := compositionRecover (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    (out.relabel j) xs ys ht'
    (fun i => Fin.cases hr' (Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i)
  let A := programGraph (guard V) (suc z) ys
  apply formulaCases A
  · have hp : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := successorBranchElim (guard V) (.projection (1 : Fin 3)) (.projection 0)
      (out.relabel j) z ys hp (withHyp hc A)
    have he := valueUnique (.projection (0 : Fin 3)) (out.relabel j) candidate ys ho (projectionValue 0 ys)
    exact replaceOutput observer (mark.relabel j) (cutoff.relabel j) (out.relabel j) candidate
      (input.relabel j) (parameter.relabel j) he
      (hR body beta (A :: Theta) candidate (input.relabel j) (parameter.relabel j)
        (mark.relabel j) (cutoff.relabel j) (withHyp hRange' A) (withHyp ha' A) (withHyp hr' A))
  · have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject candidateLess
      (InternalAcceptance.conjunction (candidateValid V) sameLeft) ys
      (show Nonempty (Derivation body (A.not :: Theta) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho := zeroBranchElim (guard V) (.projection (1 : Fin 3)) (.projection 0)
      (out.relabel j) ys hz (withHyp hc A.not)
    have he := valueUnique (.projection (1 : Fin 3)) (out.relabel j) (input.relabel j) ys ho (projectionValue 1 ys)
    exact replaceOutput observer (mark.relabel j) (cutoff.relabel j) (out.relabel j) (input.relabel j)
      (input.relabel j) (parameter.relabel j) he
      (identityObserver observer (mark.relabel j) (cutoff.relabel j) (input.relabel j) (parameter.relabel j))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
