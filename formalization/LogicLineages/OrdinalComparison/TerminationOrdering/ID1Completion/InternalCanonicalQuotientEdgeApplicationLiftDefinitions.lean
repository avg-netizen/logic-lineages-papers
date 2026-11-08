module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLift
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME existing leaves, without any correctness, endpoint, success,
fixed-argument, representative-congruence or lift field. -/
abbrev Data := InternalCanonicalDescentSelection.Data

/-- Inputs are [domain,codomain,canonical function,RAW argument]. Normalize
ONLY the argument, then use the exact C = D(original raw application).
In particular the function coordinate is NOT normalized a second time. -/
def actualJ (data : Data) : Program 4 :=
  .composition (InternalCanonicalResultFoldCalibration.combine data)
    ![.projection 0, .projection 1, .projection 2,
      .composition (InternalCanonicalResultFoldCalibration.normalizer data)
        (fun _ : Fin 1 => .projection 3)]

def applicationGraph {α : Type} (data : Data)
    (out d e x a : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (actualJ data) out d e x a

/-- The exact previously selected Edge, including the SAME W leaf and the
distinct source-filtered N / unrestricted target N representatives. -/
def edgeAccepted {α : Type} (data : Data)
    (x y certificate : OrdinaryArithmetic.Term α) : Formula α :=
  InternalCanonicalQuotientEdgeSelection.edgeAccepted data x y certificate

def typedAccepted {α : Type} (data : Data)
    (value typ : OrdinaryArithmetic.Term α) : Formula α :=
  InternalCanonicalQuotientEdgeSelection.typedAccepted data value typ

/-- The total all-input semantic target is the ORIGINAL packed-target map,
applied after the ORIGINAL raw application with only its argument first sent
through that same target map. This is not the partial canonicalApplication
function, nor a new source-validity-filtered off-domain default. -/
def ApplicationCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (data : Data) : Prop :=
  ∀ v : List.Vector Nat 4,
    evaluate (actualJ data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.applicationValue (List.Vector.ofFn
          ![v.get 0, v.get 1, v.get 2,
            InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
              (v.get 3)]))

/-- A symbolic helper for the actual raw parent and its actual N result.
Only child validity/tags, codomain membership, the actual N(f)=x graph,
raw application and actualJ graphs occur. Parent validity, G, child/parent
success, a fixed argument and representative congruence are NOT premises. -/
def representativePremises {α : Type} (data : Data)
    (arrow d e f a parent x out : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
        InternalOriginalStepGuard.one f ⊓
      (graph1 InternalUnpair.left arrow f ⊓
        (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
            InternalOriginalStepGuard.one a ⊓
          (graph1 InternalUnpair.left d a ⊓
            (graph1 data.member InternalOriginalStepGuard.one e ⊓
              (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) x f ⊓
                (graph4 application parent d e f a ⊓
                  applicationGraph data out d e x a)))))))

/-- Both parent source validity and its actual successful fold output are
conclusions. The output invariant is V(out), left(out)=e and T(out)=out. -/
def representativeConclusion {α : Type} (data : Data)
    (parent out e : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
      InternalOriginalStepGuard.one parent ⊓
    InternalCanonicalResultFoldInvariant.certifiedOutput data.oldValidity
      data.oldEdge.targetRepresentative data.member out parent e

def applicationPremises {α : Type} (data : Data) (sigma tau : Ty)
    (x a out : OrdinaryArithmetic.Term α) : Formula α :=
  typedAccepted data x (numeral (typeNumber (.arrow sigma tau))) ⊓
    (typedAccepted data a (numeral (typeNumber sigma)) ⊓
      applicationGraph data out (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x a)

/-- y is not assumed typed. Both applications use the same RAW argument a;
actualJ itself computes N(a). No N(a)=a or N(x)=x hypothesis is present. -/
def corePremises {α : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other : OrdinaryArithmetic.Term α) : Formula α :=
  typedAccepted data x (numeral (typeNumber (.arrow sigma tau))) ⊓
    (typedAccepted data a (numeral (typeNumber sigma)) ⊓
      (edgeAccepted data x y certificate ⊓
        (applicationGraph data out (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x a ⊓
          applicationGraph data other (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y a)))

/-- The unchanged edge/application/step-lift constructors use RAW a, never
N(a). These are the actual certificate fields, not newly chosen endpoints. -/
def constructorWitnesses {α : Type} (sigma tau : Ty)
    (a certificate s t k sourceApp targetApp liftedStep lifted : OrdinaryArithmetic.Term α) : Formula α :=
  InternalApplicationCertificateConstructors.liftPremises
      (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      a certificate s t k sourceApp targetApp liftedStep ⊓
    graph3 edgeCode lifted sourceApp targetApp liftedStep

/-- Exact witness-free interface. Original edgeLift has input order
[domain,codomain,RAW argument,certificate], with no normalized substitute. -/
def liftPremises {α : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other lifted : OrdinaryArithmetic.Term α) : Formula α :=
  corePremises data sigma tau x y a certificate out other ⊓
    graph4 edgeLift lifted (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      a certificate

def typedOutputs {α : Type} (data : Data) (tau : Ty)
    (out other : OrdinaryArithmetic.Term α) : Formula α :=
  typedAccepted data out (numeral (typeNumber tau)) ⊓
    typedAccepted data other (numeral (typeNumber tau))

/-- Properties of ONE fixed shared selection, not fields or assumed proof
suppliers. Closed-type membership calibration is discharged by that selection. -/
def InternalLaws (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty) (α : Type) (Delta : List (Formula α)),
    (∀ (x a out : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((applicationPremises data sigma tau x a out).imp
          (typedAccepted data out (numeral (typeNumber tau)))))) ∧
    ((∀ (x y a certificate out other lifted : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((liftPremises data sigma tau x y a certificate out other lifted).imp
          (edgeAccepted data out other lifted)))) ∧
      (∀ (x y a certificate out other lifted : OrdinaryArithmetic.Term α),
        Nonempty (Derivation body Delta
          ((liftPremises data sigma tau x y a certificate out other lifted).imp
            (typedOutputs data tau out other)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLift
