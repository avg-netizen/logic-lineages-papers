module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Local exact adapter between the original raw path-lift and the literal
final positive guard. Both supplied actualJ outputs retain their ORIGINAL
applicationPremises. In the unqualified outer lift, successor typing is
derived from the original source certificate, not added to its antecedent.
The mapped UNGUARDED acceptance below is the checked R003 conclusion.

No calibration, semantic shape, function N-fixedness, successful run,
measure law or application compatibility field is assumed. The same global
selectedData/window/oldStep and raw parameter occur in every graph. -/
def ActualGuardedPositiveApplicationLift : Prop :=
  ∀ (body : Positive (Fin 1)) (base : Data) (window : Program 1) (oldStep : Program 4),
  let selected := SpineApplicationTargets.selectedData base window
  let edge := edgeChecker selected oldStep
  ∀ (α : Type) (Delta : List (Formula α))
    (arrow d e f g a out other certificate mapped parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 (BottomRepresentative.windowAt window) InternalOriginalStepGuard.one f parameter ⊓
      (InternalOriginalUniformApplicationTyping.applicationPremises selected arrow d e f a out parameter ⊓
        (InternalOriginalUniformApplicationTyping.applicationPremises selected arrow d e g a other parameter ⊓
          (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure edge
              f g certificate parameter ⊓
            InternalParameterizedPathChecker.positiveGraph edge out other mapped parameter)))).imp
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure edge
        out other mapped parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationTargets
