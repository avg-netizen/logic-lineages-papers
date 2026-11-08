module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every input, including malformed raw codes. The right sides name the
unchanged source functions and their literal original pair expression. -/
def ExactOriginalCalibration : Prop :=
  (∀ v : List.Vector Nat 4, evaluate packedApplication v =
    Nat.pair (v.get 1) (Nat.pair 2 (Nat.pair (v.get 0) (Nat.pair (v.get 2) (v.get 3))))) ∧
  (∀ v : List.Vector Nat 4, evaluate application v = ApplicationCertificateLift.applicationValue v) ∧
  (∀ v : List.Vector Nat 1, evaluate stepLift v = ApplicationCertificateLift.stepValue v) ∧
  (∀ v : List.Vector Nat 3, evaluate edgeCode v =
    NumberedNumericQuotientEdge.edgeCertificateNumber (v.get 0) (v.get 1) (v.get 2)) ∧
  (∀ v : List.Vector Nat 1,
    evaluate source v = ApplicationCertificateLiftEdge.sourceOf (v.get 0) ∧
    evaluate target v = ApplicationCertificateLiftEdge.targetOf (v.get 0) ∧
    evaluate step v = ApplicationCertificateLiftEdge.stepOf (v.get 0)) ∧
  (∀ v : List.Vector Nat 4, evaluate edgeLift v = ApplicationCertificateLiftEdge.edgeValue v)

def ActualOriginalEdgeSelectors : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (certificate s t k : OTerm α),
  Nonempty (Derivation body []
    ((graph3 edgeCode certificate s t k).imp (selectors certificate s t k)))

/-- Arbitrary code and all three original selector outputs; no canonical-code
or successful-decoding premise is introduced. -/
def ActualOriginalEdgeReconstruction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (certificate s t k : OTerm α),
  Nonempty (Derivation body []
    ((selectors certificate s t k).imp (graph3 edgeCode certificate s t k)))

def ActualOriginalApplicationPayloadEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (d e f a fp ap out : OTerm α),
  Nonempty (Derivation body []
    ((graph1 InternalUnpair.right fp f ⊓ graph1 InternalUnpair.right ap a).imp
      ((graph4 application out d e f a).iff (graph4 packedApplication out d e fp ap))))

/-- Generated source payloads are extracted through the ORIGINAL pair inverse.
The two original outer type fields remain unrestricted. -/
def ActualOriginalPackedApplicationEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (d e f a ftype atype fp ap out : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalPairing.pairing f ftype fp ⊓ graph2 InternalPairing.pairing a atype ap).imp
      ((graph4 application out d e f a).iff (graph4 packedApplication out d e fp ap))))

def ActualOriginalStepPrefixEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (certificate path payload prefixed out : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalPairing.pairing certificate path payload ⊓
      graph2 InternalListCodec.consCode prefixed positionTerm path).imp
      ((graph1 stepLift out certificate).iff (graph2 InternalPairing.pairing out prefixed payload))))

/-- Preserve the very same replacement/root payload on every raw source code. -/
def ActualOriginalStepPayloadPreserved : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (certificate path payload out : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalPairing.pairing certificate path payload ⊓ graph1 stepLift out certificate).imp
      (graph1 InternalUnpair.right payload out)))

/-- Any original left selector of the transformed step is precisely the
original appFunction-prefix cons; the replacement/root payload is unchanged. -/
def ActualOriginalStepDestruction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (certificate path payload out prefixed : OTerm α),
  Nonempty (Derivation body []
    ((graph2 InternalPairing.pairing certificate path payload ⊓
      (graph1 stepLift out certificate ⊓ graph1 InternalUnpair.left prefixed out)).imp
      (graph2 InternalListCodec.consCode prefixed positionTerm path ⊓
        graph1 InternalUnpair.right payload out)))

/-- Bidirectional internal commutation on the exact supplied edge fields and
their exact transformed codes, including malformed/off-domain numeric inputs. -/
def ActualOriginalEdgeLiftEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (d e a certificate s t k s' t' k' out : OTerm α),
  Nonempty (Derivation body []
    ((liftPremises d e a certificate s t k s' t' k').imp
      ((graph4 edgeLift out d e a certificate).iff (graph3 edgeCode out s' t' k'))))

def ActualOriginalLiftedEdgeSelectors : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (d e a certificate s t k s' t' k' out : OTerm α),
  Nonempty (Derivation body []
    ((liftPremises d e a certificate s t k s' t' k' ⊓ graph4 edgeLift out d e a certificate).imp
      (selectors out s' t' k')))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsTargets
