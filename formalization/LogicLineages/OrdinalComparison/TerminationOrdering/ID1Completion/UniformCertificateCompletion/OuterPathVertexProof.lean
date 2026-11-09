module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPathVertexProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Actual typed input graphs and the actual pair activate the literal
uniform vertex. No activation or path invariant is added to the caller. -/
theorem rawApplication (n : Nat) (window : Program 1) (hw : Path.windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (data : Data) (oldVertex : Program 5)
    (sigma tau : Ty) (parameter gammaCode x argument out : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.parameterGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hf : Nonempty (Derivation body Delta
      (typedAccepted data x (numeral (typeNumber (.arrow sigma tau))) parameter)))
    (ha : Nonempty (Derivation body Delta
      (typedAccepted data argument (numeral (typeNumber sigma)) parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph5 (Path.vertex data window oldVertex) out parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x argument parameter)) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hcoordinates := OuterResultSupportProof.outputCoordinates parameter (numeral context) gammaCode hp
  have hi := PathInvariantProof.invariantAccept context data sigma tau parameter
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x
    (andIntro (andLeft hcoordinates)
      (andIntro (PathSupportProof.equalReflexive (numeral (typeNumber sigma)))
        (andIntro (PathSupportProof.equalReflexive (numeral (typeNumber tau))) (andIntro hf ha))))
  have hactive := PathInvariantProof.invariantActivation n window hw symbols S table hS data sigma tau
    parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x hi
  exact PathSupportProof.vertexRecover data window oldVertex
    (Path.arguments parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)
    out hactive hv

theorem outputTyped (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (parameter gammaCode x argument out : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.parameterGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hf : Nonempty (Derivation body Delta
      (typedAccepted (OuterSelection.data base window) x
        (numeral (typeNumber (.arrow sigma tau))) parameter)))
    (ha : Nonempty (Derivation body Delta
      (typedAccepted (OuterSelection.data base window) argument (numeral (typeNumber sigma)) parameter)))
    (hj : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph (OuterSelection.data base window) out
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x argument parameter))) :
    Nonempty (Derivation body Delta
      (typedAccepted (OuterSelection.data base window) out (numeral (typeNumber tau)) parameter)) :=
  InternalOriginalUniformApplicationTypingProof.runtimeApplicationTyped
    n arity (OuterSelectionCalibrationProof.preData base window)
    (OuterSelectionCalibrationProof.preCalibrated n arity base hc window hw)
    symbols S table hS sigma tau parameter gammaCode x argument out
    (andIntro hp (andIntro hf (andIntro ha hj)))

/-- Pay every ORIGINAL generic actualJ premise from the unchanged runtime
input. In particular codomain membership follows from normalized arrow
membership and source subtype closure; it is not added to the lift input. -/
theorem applicationPremises (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (parameter gammaCode x argument out : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.parameterGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hf : Nonempty (Derivation body Delta
      (typedAccepted (OuterSelection.data base window) x
        (numeral (typeNumber (.arrow sigma tau))) parameter)))
    (ha : Nonempty (Derivation body Delta
      (typedAccepted (OuterSelection.data base window) argument (numeral (typeNumber sigma)) parameter)))
    (hj : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph (OuterSelection.data base window) out
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x argument parameter))) :
    Nonempty (Derivation body Delta
      (InternalOriginalUniformApplicationTyping.applicationPremises (OuterSelection.data base window)
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
        (numeral (typeNumber tau)) x argument out parameter)) := by
  let data := OuterSelection.data base window
  have hArrow := andLeft (InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data) data.member
    x (numeral (typeNumber (.arrow sigma tau))) parameter hf)
  have hmember := InternalOriginalUniformApplicationTypingMembershipProof.codomainMembership
    n arity (OuterSelectionCalibrationProof.preData base window)
    (OuterSelectionCalibrationProof.preCalibrated n arity base hc window hw)
    symbols S table hS sigma tau parameter gammaCode hp hArrow
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral
    (body := body) (Gamma := Delta) (α := α) sigma tau
  exact andIntro har (andIntro hmember (andIntro hf (andIntro ha hj)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPathVertexProof
