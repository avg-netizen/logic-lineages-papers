module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal equality at EVERY original raw input/parameter pair. No
validity, successful decoding, closed-window, child-fixedness or semantic
calibration assumption is inserted after choosing the original Data. -/
def ActualOriginalApplicationSidecarRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2,
    evaluate (representative data window) v = evaluate data.oldRepresentative v) ∧
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window)

/-- Exact AST equalities through the original once-normalized pipeline.
The eventual Data is the SAME S1 used by the new selection, not another
calibrated package. No native equality of compiled graphs is assumed. -/
def ActualOriginalApplicationSidecarSelectionIdentity : Prop :=
  (∀ (data : Data) (window : Program 1),
    let before := originalData data window
    let after := selectedData data window
    before.oldSource = BottomParameter.normalized data.oldSource ∧
    before.oldTarget = BottomParameter.normalized data.oldTarget ∧
    before.member = InternalOriginalUniformContextMembership.normalizedMember data.member ∧
    after.oldSource = before.oldSource ∧
    after.oldTarget = before.oldTarget ∧
    after.member = before.member ∧
    InternalOriginalUniformDescentSelection.validity after =
      InternalOriginalUniformDescentSelection.validity before ∧
    InternalParameterizedCanonicalResultFold.rootGuard after =
      InternalParameterizedCanonicalResultFold.rootGuard before ∧
    OriginalFunctionNeutrality.active (baseData data window) window =
      OriginalFunctionNeutrality.active data window ∧
    OriginalFunctionNeutrality.active data window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (InternalOriginalUniformDescentSelection.validity before)) ∧
  ∀ p : GlobalSourcePackage.Inputs,
    (finalInputs p).window = p.window ∧
    OuterSelection.data (finalInputs p).base (finalInputs p).window =
      selectedData p.base p.window

/-- The actual window graph ignores only its input coordinate. Both
internal implications retain the SAME symbolic parameter and original
window Program, with no native-to-internal inference or validity premise. -/
def ActualOriginalApplicationSidecarWindowIndependence : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (window : Program 1) (input other parameter : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter).iff
      (OriginalFunctionNeutrality.windowGraph window other parameter)))

/-- Parent validity opens the unchanged original guard. The exact raw
application equation requires neither a window premise nor supplied child
success, type, bound, canonicality or fixedness. All child graphs concern
this sidecar at the SAME original parameter. -/
def ActualOriginalApplicationSidecarApplicationEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (InternalApplicationCertificateConstructors.graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
        InternalOriginalStepGuard.one parent parameter ⊓
        (InternalApplicationCertificateConstructors.graph2 (fold data window) functionOut fn parameter ⊓
          InternalApplicationCertificateConstructors.graph2 (fold data window) argumentOut arg parameter))).imp
      ((InternalApplicationCertificateConstructors.graph2 (fold data window) out parent parameter).iff
        (InternalApplicationCertificateConstructors.graph4 InternalApplicationCertificateConstructors.application
          out d e functionOut argumentOut))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
