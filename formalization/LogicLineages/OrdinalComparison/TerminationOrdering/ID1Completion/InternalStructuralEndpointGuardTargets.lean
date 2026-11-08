module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalStructuralEndpointGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Select one actual unary membership Program for each fixed, arbitrary S,
before quantifying every natural input. No closure condition is assumed. -/
def ActualOriginalMembershipProgramExists : Prop :=
  ∀ S : List Ty, ∃ member : Program 1, MembershipCalibrated S member

/-- The concrete AST equals the UNCHANGED endpointValue on every five-tuple.
The source and argument retain the original universe filters; the target has
only original packed decoding. No successful-decoding, valid-input or subtype-
closure premise is introduced. The total original type codec eliminates the
need for separate domain/codomain-validity leaves, not any original guard. -/
def ActualOriginalStructuralEndpointCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  MembershipCalibrated S member →
  InternalApplicationStepPeel.EndpointCalibrated n arity symbols S Gamma
    (endpoint validity member)

/-- Internal factorization AND introduction, for arbitrary Program leaves and
symbolic inputs. Only the actual consCode arrow graph is assumed. Acceptance
derives all three raw tag graphs as well as the shared validity and membership
graphs; conversely those graphs derive acceptance. No semantic calibration,
decoded object, extra type-validity leaf or truth-to-derivability rule appears. -/
def ActualOriginalEndpointAcceptanceAtArrow : Prop :=
  ∀ (body : Positive (Fin 1)) (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (α : Type) (arrow d e s t a : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalListCodec.consCode arrow d e).imp
      ((accepted validity member d e s t a).iff
        (requirements validity member arrow d e s t a))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardTargets
