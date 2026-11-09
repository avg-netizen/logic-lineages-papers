module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawLiftProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open SourceComputabilityCompletion
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Lift the SAME original raw path, then restore both final positive
checker guards from the two actual application premise blocks. The raw
function is never replaced by its normal form. -/
theorem rawLift (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldStep : Program 4) (oldVertex : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (parameter gammaCode x y argument witness out other mapped : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.parameterGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hf : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.applicationPremises (OuterSelection.data base window)
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) x argument out parameter)))
    (hg : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.applicationPremises (OuterSelection.data base window)
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) y argument other parameter)))
    (hraw : Nonempty (Derivation body Delta
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker (OuterSelection.data base window) oldStep) x y witness parameter)))
    (hvertexF : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) out parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)))
    (hvertexG : Nonempty (Derivation body Delta
      (graph5 (Path.vertex (OuterSelection.data base window) window oldVertex) other parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument y)))
    (hm : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph (Path.vertex (OuterSelection.data base window) window oldVertex)
        mapped witness parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument))) :
    Nonempty (Derivation body Delta
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker (OuterSelection.data base window) oldStep) out other mapped parameter)) := by
  let data := OuterSelection.data base window
  let edge := edgeChecker data oldStep
  let xs : Fin 4 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons witness (Fin.cons parameter Fin.elim0)))
  have hguard := conjunctionRecover (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
    (InternalAcceptance.conjunction (PositiveGuard.spineGuard BottomSpineMeasure.measure)
      (InternalParameterizedPathChecker.checker edge true)) xs hraw
  have hpath := andRight (conjunctionRecover (PositiveGuard.spineGuard BottomSpineMeasure.measure)
    (InternalParameterizedPathChecker.checker edge true) xs (andRight hguard))
  have htypedF := andLeft (andRight (andRight hf))
  have htypedA := andLeft (andRight (andRight (andRight hf)))
  have inputs : Nonempty (Derivation body Delta
      (Path.positivePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        data oldStep window oldVertex sigma tau
        parameter gammaCode x y argument witness out other mapped)) :=
    andIntro hp (andIntro htypedF (andIntro htypedA
      (andIntro hpath (andIntro hvertexF (andIntro hvertexG hm)))))
  obtain ⟨rule⟩ := PathProof.actualOriginalUniformPositiveApplicationPathLift
    n arity (OuterSelectionCalibrationProof.preData base window)
    (OuterSelectionCalibrationProof.preCalibrated n arity base hc window hw)
    window hw symbols S table hS oldStep oldVertex body α Delta sigma tau
    parameter gammaCode x y argument witness out other mapped
  obtain ⟨inputs⟩ := inputs
  have lifted : Nonempty (Derivation body Delta
      (InternalParameterizedPathChecker.positiveGraph edge out other mapped parameter)) :=
    ⟨Derivation.implicationElimination rule inputs⟩
  have hwindow := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Delta) (α := α) window
    (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (OuterWindowProof.closedWindowEvaluation n window hw symbols S table hS)
  have hparameterWindow := OuterWindowProof.parameterWindow window
    (OrdinaryArithmeticQuotient.contextCode symbols S table) x parameter gammaCode hwindow hp
  exact GuardedPositiveApplicationProof.guardedLift base window oldStep
    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    x y argument out other witness mapped parameter
    (andIntro hparameterWindow (andIntro hf (andIntro hg (andIntro hraw lifted))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterRawLiftProof
