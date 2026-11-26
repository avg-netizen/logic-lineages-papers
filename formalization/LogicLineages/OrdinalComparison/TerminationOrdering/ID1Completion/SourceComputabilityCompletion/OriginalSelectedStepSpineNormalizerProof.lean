module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTransitionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineNormalizerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open OriginalSelectedStepSpineStateProof OriginalSelectedStepSpineTransitionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The SAME original raw path drives the original repeat. Its actual code
is bound internally; the parameter remains a separate, unchanged input. -/
theorem normalizerBackward (endpoint : Program 6) (state normalized parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (normalizerGraph endpoint normalized state parameter)))
    (hg : Nonempty (Derivation body Gamma (stateGuard normalized parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) := by
  apply programCases InternalApplicationStepPeel.rawPath (Fin.cons state Fin.elim0) _
  intro beta j Delta code hj hp
  rw [stateGuardRename]
  simp only [consTermRename,emptyRename] at hp
  have hn' := renameInto hn j Delta hj
  rw [normalizerGraphRename] at hn'
  have hg' := renameInto hg j Delta hj
  rw [stateGuardRename] at hg'
  let xs : Fin 2 → OTerm beta :=
    Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hr : Nonempty (Derivation body Delta (repeatGraph (transitionP endpoint)
      (normalized.relabel j) code (state.relabel j) (parameter.relabel j))) := by
    apply compositionRecover (repeatP (transitionP endpoint))
      ![liftP InternalApplicationStepPeel.rawPath,.projection 0,.projection 1]
      (normalized.relabel j) xs
      (Fin.cons code (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) hn'
    intro i
    exact Fin.cases
      (liftValue InternalApplicationStepPeel.rawPath code (state.relabel j) (parameter.relabel j) hp)
      (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
        (fun q => Fin.elim0 q))) i
  exact OriginalSelectedStepSpineRepeatProof.backwardValue (transitionP endpoint) stateTest
    (transitionBackward endpoint) code (state.relabel j) (normalized.relabel j)
    (parameter.relabel j) hr hg'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineNormalizerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineNormalizerProof
