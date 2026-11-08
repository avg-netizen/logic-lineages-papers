module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalCertifiedQuotientEdgeApplicationLift

/-- Genuine internal transport of the strengthened selected step. The checked
base rule supplies base acceptance. Target-parent source validity must follow
by rebuilding the duplicate endpoint (t,t,a); parent good runs must follow
from certified-fold closure and internal totality, never semantic H=1
reflection. This prerequisite needs neither calibration nor fixed-point
acceptance of the argument, and no parent acceptance is assumed. -/
def ActualOriginalCertifiedApplicationStepClosure : Prop :=
  ∀ (data : Data) (body : Positive (Fin 1)) (α : Type)
    (arrow d e s t a k sourceApp targetApp liftedStep : OTerm α),
  Nonempty (Derivation body []
    ((stepLiftPremises data arrow d e s t a k sourceApp targetApp liftedStep).imp
      (InternalCertifiedSourceGuardSelection.stepAccepted data sourceApp targetApp liftedStep)))

/-- Constructor-witness version on the SAME selected ASTs. Only the member
leaf is externally calibrated, exclusively for CLOSED type-code computations.
The actual selected typed/step/representative guards derive all raw validity,
tag, endpoint, success and fixed-argument facts inside the derivation. No
raw-validity, endpoint or representative-congruence hypothesis is inserted. -/
def ActualOriginalCertifiedEncodedQuotientEdgeApplicationLift : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type)
    (x y a certificate out other s t k sourceApp targetApp liftedStep lifted : OTerm α),
  Nonempty (Derivation body []
    ((corePremises data sigma tau x y a certificate out other ⊓
      constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted).imp
      (coreAccepted data out other lifted)))

/-- LOCAL original core-edge application lift with no exposed raw witnesses.
Original selector/constructor witnesses are obtained by internal Program
totality, and edgeLift commutation preserves the actual supplied certificate.
The two outputs are the literal combine results, not newly chosen endpoints.
No target typing, output invariant, outer typed-edge wrapper, context dispatch,
path theorem or CertifiedApplicationLift is included in this conclusion. -/
def ActualOriginalCertifiedQuotientEdgeApplicationLift : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type)
    (x y a certificate out other lifted : OTerm α),
  Nonempty (Derivation body []
    ((liftPremises data sigma tau x y a certificate out other lifted).imp
      (coreAccepted data out other lifted)))

/-- ONE shared original leaf selection precedes every type, body and symbolic
term. Its exact selected guards/representatives retain the all-input original
calibrations, including zero and malformed behavior, and its original core
has the local internal rule above. There is no full-context selection or
uniform compiler assertion, output typed invariant, outer typed-edge result,
path lifting or discharge of the full CertifiedApplicationLift premise. -/
def ActualOriginalSelectedCertifiedQuotientEdgeApplicationLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : Data,
    InternalCertifiedSourceGuardSelection.Calibrated n arity symbols S Gamma table data ∧
      (InternalCertifiedSourceGuardSelection.SelectedCalibrated n arity symbols S Gamma table data ∧
        ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type)
          (x y a certificate out other lifted : OTerm α),
        Nonempty (Derivation body []
          ((liftPremises data sigma tau x y a certificate out other lifted).imp
            (coreAccepted data out other lifted))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftTargets
