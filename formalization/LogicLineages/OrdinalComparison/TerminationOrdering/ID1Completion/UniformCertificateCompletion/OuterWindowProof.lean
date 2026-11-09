module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem closedWindowEvaluation (n : Nat) (window : Program 1) (hw : Path.windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    evaluate window (List.Vector.ofFn ![OrdinaryArithmeticQuotient.contextCode symbols S table]) = 1 := by
  rw [hw]
  exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hS

/-- The SAME original pair supplies the context for the selected
representative/application window graph at an arbitrary symbolic Gamma. -/
theorem parameterWindow (window : Program 1) (context : Nat) (function parameter gammaCode : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode))) :
    Nonempty (Derivation body Delta
      (graph2 (SourceComputabilityCompletion.BottomRepresentative.windowAt window) (suc z) function parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons function (Fin.cons parameter Fin.elim0)
  have hl := andLeft (OuterResultSupportProof.outputCoordinates parameter (numeral context) gammaCode hp)
  exact unaryValue window (leftOf (.projection (1 : Fin 2))) (suc z) (numeral context) xs hw
    (unaryValue InternalUnpair.left (.projection (1 : Fin 2)) (numeral context) parameter xs
      hl (projectionValue 1 xs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
