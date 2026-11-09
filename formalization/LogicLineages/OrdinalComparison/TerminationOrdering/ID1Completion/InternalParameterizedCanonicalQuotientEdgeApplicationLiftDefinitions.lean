module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLift
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev applicationGraph {α : Type} (data : Data)
    (out d e x a parameter : OTerm α) : Formula α :=
  InternalParameterizedCanonicalResultFold.applicationGraph data out d e x a parameter

abbrev typedAccepted {α : Type} (data : Data) (value typ parameter : OTerm α) : Formula α :=
  InternalParameterizedQuotientEdgeChecker.typedAccepted data value typ parameter

abbrev edgeAccepted {α : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) : Formula α :=
  InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate parameter

/-- The exact two actualJ graphs retain the RAW argument and only normalize
it inside actualJ. Target function typing is derived from the SAME edge. -/
def applicationInputs {α : Type} (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other parameter : OTerm α) : Formula α :=
  typedAccepted data x arrow parameter ⊓
    (typedAccepted data a d parameter ⊓
      (edgeAccepted data oldStep x y certificate parameter ⊓
        (applicationGraph data out d e x a parameter ⊓
          applicationGraph data other d e y a parameter)))

/-- The generic arithmetic rule permits arbitrary type codes. Its explicit
arrow graph and codomain membership are discharged by the normalized source
package in the runtime-context theorem; they are not hidden correctness fields. -/
def corePremises {α : Type} (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other parameter : OTerm α) : Formula α :=
  (graph2 InternalListCodec.consCode arrow d e ⊓
    graph2 data.member InternalOriginalStepGuard.one e parameter) ⊓
      applicationInputs data oldStep arrow d e x y a certificate out other parameter

def constructorWitnesses {α : Type}
    (d e a certificate s t k sourceApp targetApp liftedStep lifted : OTerm α) : Formula α :=
  InternalApplicationCertificateConstructors.liftPremises
      d e a certificate s t k sourceApp targetApp liftedStep ⊓
    graph3 edgeCode lifted sourceApp targetApp liftedStep

def liftPremises {α : Type} (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other lifted parameter : OTerm α) : Formula α :=
  corePremises data oldStep arrow d e x y a certificate out other parameter ⊓
    graph4 edgeLift lifted d e a certificate

def typedOutputs {α : Type} (data : Data) (e out other parameter : OTerm α) : Formula α :=
  typedAccepted data out e parameter ⊓ typedAccepted data other e parameter

def result {α : Type} (data : Data) (oldStep : Program 4)
    (e out other lifted parameter : OTerm α) : Formula α :=
  edgeAccepted data oldStep out other lifted parameter ⊓ typedOutputs data e out other parameter

/-- The original context is fixed but its shared runtime Gamma is symbolic.
The antecedent contains no codomain-membership, target-typing, raw-endpoint
validity, successful-fold or representative-congruence premise. -/
def runtimePremises {α : Type} (window : Nat) (data : Data) (oldStep : Program 4)
    (sigma tau : Ty) (parameter gammaCode x y a certificate out other lifted : OTerm α) : Formula α :=
  InternalOriginalUniformApplicationTyping.parameterGraph window parameter gammaCode ⊓
    (applicationInputs data oldStep (numeral (typeNumber (.arrow sigma tau)))
      (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      x y a certificate out other parameter ⊓
      graph4 edgeLift lifted (numeral (typeNumber sigma)) (numeral (typeNumber tau)) a certificate)

/-- All raw arguments retain the original packed-target representative after
the original raw application with only its argument first normalized. -/
def ApplicationCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  ∀ v : List.Vector Nat 4,
  evaluate (InternalParameterizedCanonicalResultFold.actualJ data) (List.Vector.ofFn
      ![v.get 0,v.get 1,v.get 2,v.get 3,
        InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table]) =
    InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
      (ApplicationCertificateLift.applicationValue (List.Vector.ofFn
        ![v.get 0,v.get 1,v.get 2,
          InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma (v.get 3)]))

def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun typ => typ ∈ S) →
    InternalParameterizedPathChecker.EdgeCalibrated n arity symbols S Gamma table
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
      (InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table) ∧
    ApplicationCalibrated n arity symbols S Gamma table data

/-- The original closed types and window vary outside an arbitrary internal
body/context. The shared runtime Gamma code and every value remain symbolic. -/
def InternalRuntimeLaw (n : Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode x y a certificate out other lifted : OTerm α),
  Nonempty (Derivation body Delta
    ((runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        data oldStep sigma tau parameter gammaCode x y a certificate out other lifted).imp
      (result data oldStep (numeral (typeNumber tau)) out other lifted parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLift
