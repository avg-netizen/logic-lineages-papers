module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceProof
open ParameterSlice
open InternalOriginalUniformDescentSelection
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalParameterizedCanonicalResultFold (rootGuard leaf combine foldN actualJ)
open InternalParameterizedApplicationResultFoldCalibration (semanticFoldP)
open InternalParameterizedApplicationResultFoldCalibrationProof
open InternalParameterizedApplicationResultStack (wireP)
open InternalParameterizedApplicationResultStackEvaluationProof (wirePEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Only the actual old representative and source-validity slices enter
one transition. The raw input and every comparison are unchanged. -/
theorem transitionSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition
      data.oldRepresentative (validity data)) (ofFn ![value,p]) =
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition
      data.oldRepresentative (validity data)) (ofFn ![value,q]) := by
  simp only [transitionEvaluation,h.1,h.2.1]

theorem normalizerSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (InternalParameterizedBoundedDescentNormalizer.normalizer
      data.oldRepresentative (validity data)) (ofFn ![value,p]) =
    evaluate (InternalParameterizedBoundedDescentNormalizer.normalizer
      data.oldRepresentative (validity data)) (ofFn ![value,q]) := by
  rw [normalizerEvaluation,normalizerEvaluation,funext (transitionSlice data p q h)]

theorem representativeSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (representative data) (ofFn ![value,p]) =
      evaluate (representative data) (ofFn ![value,q]) := by
  simp only [representative,fallbackEvaluation,h.2.1,h.1,normalizerSlice data p q h]

theorem scalarSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (SourceComputabilityCompletion.RawScalar.checker data) (ofFn ![value,p]) =
      evaluate (SourceComputabilityCompletion.RawScalar.checker data) (ofFn ![value,q]) := by
  simp only [SourceComputabilityCompletion.RawScalarEvaluationProof.checkerEvaluation,
    h.2.1,transitionSlice data p q h]

theorem typedSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value typ : Nat) :
    evaluate (selectedTyped data) (ofFn ![value,typ,p]) =
      evaluate (selectedTyped data) (ofFn ![value,typ,q]) := by
  simp only [selectedTyped,typedEvaluation,h.2.2,h.2.1,transitionSlice data p q h]

/-- The selector reads only the original value; the supplied parameter
is passed unchanged to the same binary callback. -/
theorem wireSlice (P : Program 2) (p q : Nat)
    (h : ∀ value : Nat, evaluate P (ofFn ![value,p]) = evaluate P (ofFn ![value,q]))
    (selector : Program 1) (value : Nat) :
    evaluate (wireP P (fun _ : Fin 1 => selector)) (ofFn ![value,p]) =
      evaluate (wireP P (fun _ : Fin 1 => selector)) (ofFn ![value,q]) := by
  rw [wirePEvaluation,wirePEvaluation]
  change evaluate P (ofFn ![evaluate selector (ofFn ![value]),p]) =
    evaluate P (ofFn ![evaluate selector (ofFn ![value]),q])
  exact h _

theorem rootGuardSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (rootGuard data) (ofFn ![value,p]) =
      evaluate (rootGuard data) (ofFn ![value,q]) := by
  simp only [rootGuard,conjunctionEvaluation,h.2.1,
    wireSlice (validity data) p q h.2.1,wireSlice data.member p q h.2.2]

theorem leafSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (leaf data) (ofFn ![value,p]) =
      evaluate (leaf data) (ofFn ![value,q]) :=
  representativeSlice data p q h value

theorem combineSlice (data : Data) (p q : Nat) (h : Atomic data p q)
    (domain codomain function argument : Nat) :
    evaluate (combine data) (ofFn ![domain,codomain,function,argument,p]) =
      evaluate (combine data) (ofFn ![domain,codomain,function,argument,q]) := by
  change evaluate (leaf data) (ofFn ![evaluate InternalApplicationCertificateConstructors.application
      (ofFn ![domain,codomain,function,argument]),p]) =
    evaluate (leaf data) (ofFn ![evaluate InternalApplicationCertificateConstructors.application
      (ofFn ![domain,codomain,function,argument]),q])
  exact leafSlice data p q h _

/-- The original semantic fold is a function of three callback functions.
Their pointwise slice equalities suffice, with no new recursion principle. -/
theorem semanticFoldSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    semanticFoldP (rootGuard data) (leaf data) (combine data) value p =
      semanticFoldP (rootGuard data) (leaf data) (combine data) value q := by
  have hg := funext (rootGuardSlice data p q h)
  have hl := funext (leafSlice data p q h)
  have hc : (fun d e f a => evaluate (combine data) (ofFn ![d,e,f,a,p])) =
      (fun d e f a => evaluate (combine data) (ofFn ![d,e,f,a,q])) := by
    funext d e f a
    exact combineSlice data p q h d e f a
  unfold semanticFoldP
  rw [hg,hl,hc]

/-- Transfer the SAME literal bounded-stack Program through its existing
all-input semantic calibration. No successful-run premise is introduced. -/
theorem foldSlice (data : Data) (p q : Nat) (h : Atomic data p q) (value : Nat) :
    evaluate (foldN data) (ofFn ![value,p]) =
      evaluate (foldN data) (ofFn ![value,q]) := by
  have hp := (actualOriginalParameterizedBoundedResultFoldCalibration
    (rootGuard data) (leaf data) (combine data) value p).2
  have hq := (actualOriginalParameterizedBoundedResultFoldCalibration
    (rootGuard data) (leaf data) (combine data) value q).2
  exact hp.trans ((semanticFoldSlice data p q h value).trans hq.symm)

/-- actualJ normalizes only its raw argument and then uses one combine. -/
theorem applicationSlice (data : Data) (p q : Nat) (h : Atomic data p q)
    (domain codomain function argument : Nat) :
    evaluate (actualJ data) (ofFn ![domain,codomain,function,argument,p]) =
      evaluate (actualJ data) (ofFn ![domain,codomain,function,argument,q]) := by
  change evaluate (combine data)
      (ofFn ![domain,codomain,function,evaluate (foldN data) (ofFn ![argument,p]),p]) =
    evaluate (combine data)
      (ofFn ![domain,codomain,function,evaluate (foldN data) (ofFn ![argument,q]),q])
  rw [foldSlice data p q h argument]
  exact combineSlice data p q h _ _ _ _

theorem actualOriginalCompositeParameterSliceCongruence :
    ParameterSliceTargets.ActualOriginalCompositeParameterSliceCongruence := by
  intro data p q h
  exact ⟨transitionSlice data p q h,representativeSlice data p q h,
    scalarSlice data p q h,typedSlice data p q h,foldSlice data p q h,
    applicationSlice data p q h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceProof
