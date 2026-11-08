module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalCanonicalQuotientEdgeApplicationLift

/-- All four natural coordinates, including malformed and nonuniverse inputs,
retain the exact old target-representative map. The function input is not
normalized; only the argument coordinate is passed through actual N. -/
def ActualOriginalCanonicalApplicationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ApplicationCalibrated n arity symbols S Gamma data

/-- Symbolic actual-N application transport for arbitrary original leaves
and derivation contexts. All successful child/parent certificates and the
original G application opening must be derived internally from the stated
child facts. No calibration, semantic reflection or congruence law is assumed. -/
def ActualOriginalCanonicalRepresentativeApplicationTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (arrow d e f a parent x out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((representativePremises data arrow d e f a parent x out).imp
      (representativeConclusion data parent out e)))

/-- The only external leaf calibration is member, used solely for closed
type-code membership. Raw validity/tags, normalized argument invariants and
the typed result of D(original raw application) must be derived internally. -/
def ActualOriginalCanonicalApplicationTypedOutput : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type) (Delta : List (Formula α))
    (x a out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((applicationPremises data sigma tau x a out).imp
      (typedAccepted data out (numeral (typeNumber tau)))))

/-- Opened original-certificate version of the SAME-checker lift. No extra
endpoint, parent validity, good-run, target typing or fixed-argument premise
is added. Raw tags are recovered from canonical fold outputs and W's original
tag guard, never from the old typed presentation. -/
def ActualOriginalCanonicalEncodedQuotientEdgeApplicationLift : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type) (Delta : List (Formula α))
    (x y a certificate out other s t k sourceApp targetApp liftedStep lifted : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((corePremises data sigma tau x y a certificate out other ⊓
      constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted).imp
      (edgeAccepted data out other lifted)))

/-- LOCAL witness-free lifting at the EXACT selected Edge. Original Program
totality eliminates the actual certificate/application witnesses. The actual
supplied edgeLift output uses RAW a; the outputs are the supplied actualJ
graphs. No alternate checker, endpoint, normalized function or certificate. -/
def ActualOriginalCanonicalQuotientEdgeApplicationLift : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type) (Delta : List (Formula α))
    (x y a certificate out other lifted : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((liftPremises data sigma tau x y a certificate out other lifted).imp
      (edgeAccepted data out other lifted)))

/-- Both actualJ outputs have the original codomain at the SAME typed AST.
Input y typedness is derived by the canonical Edge propagation rule; it is
not added to the lift premises. No extra codomain-membership graph is assumed. -/
def ActualOriginalCanonicalQuotientEdgeApplicationTypedOutputs : Prop :=
  ∀ (S : List Ty) (data : Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type) (Delta : List (Formula α))
    (x y a certificate out other lifted : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((liftPremises data sigma tau x y a certificate out other lifted).imp
      (typedOutputs data tau out other)))

/-- ONE original Data precedes EVERY body, type, variable type, context and
symbolic term. Preserve its original and selected Edge/typed calibrations and
internal propagation, add exact actualJ calibration and its local internal
rules. This does not select a context-uniform compiler or prove a path lift,
CertifiedApplicationLift, full computability closure or paper06 lem:id1. -/
def ActualOriginalSelectedCanonicalQuotientEdgeApplicationLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : Data,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
      (InternalCanonicalQuotientEdgeSelection.SelectedCalibrated n arity symbols S Gamma table data ∧
        (ApplicationCalibrated n arity symbols S Gamma data ∧
          (InternalCanonicalQuotientEdgeSelection.InternalLaws data ∧ InternalLaws data)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
