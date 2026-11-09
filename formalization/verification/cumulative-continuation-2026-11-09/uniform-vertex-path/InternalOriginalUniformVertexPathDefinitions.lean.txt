module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPath
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data selectedTyped)
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [parameter,domain,codomain,RAWargument,value]. The original Object
decoder supplies Gamma, and the original context is the left parameter field.
The original vertex retains all its own decoding and failure behavior. -/
def oldVertexValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  ((parameterObject (v.get 4) (v.get 0)).map (fun obj =>
    ApplicationCertificateLiftPath.vertex n arity obj.1 (Nat.unpair (v.get 0)).1
      (v.get 1) (v.get 2) (v.get 3) obj.2)).getD 0

def OldVertexCalibrated (n : Nat) (arity : Fin n → Nat) (oldVertex : Program 5) : Prop :=
  ∀ v : List.Vector Nat 5, evaluate oldVertex v = oldVertexValue n arity v

/-- All four raw vertex coordinates vary at the encoded original source
parameter. No typing, decoding success, nonzero or universe premise occurs. -/
def VertexCalibratedAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (vertexProgram : Program 5) : Prop :=
  ∀ domain codomain argument value : Nat,
    evaluate vertexProgram (List.Vector.ofFn
      ![parameterCode symbols S Gamma table,domain,codomain,argument,value]) =
      ApplicationCertificateLiftPath.vertex n arity Gamma
        (OrdinaryArithmeticQuotient.contextCode symbols S table) domain codomain argument value

/-- The mapper is the unchanged original raw-list map. Only its former
context coordinate now carries the same runtime parameter as the vertex. -/
def MapCalibratedAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (vertexProgram : Program 5) : Prop :=
  ∀ domain codomain argument code : Nat,
    evaluate (InternalApplicationPathMap.pathMap vertexProgram) (List.Vector.ofFn
      ![code,parameterCode symbols S Gamma table,domain,codomain,argument]) =
      ApplicationCertificateLiftPath.liftPath n arity Gamma
        (OrdinaryArithmeticQuotient.contextCode symbols S table) domain codomain argument code

def functionTyped (data : Data) : Program 5 :=
  .composition (selectedTyped data)
    ![.projection 4,consOf (.projection 1) (.projection 2),.projection 0]

def argumentTyped (data : Data) : Program 5 :=
  .composition (selectedTyped data) ![.projection 3,.projection 1,.projection 0]

/-- Exactly the two canonical typed graphs, both at the same parameter.
There is no captured window, supplied Gamma, old typed test or N-fixed test. -/
def activation (data : Data) : Program 5 :=
  InternalAcceptance.conjunction (functionTyped data) (argumentTyped data)

/-- ActualJ receives the supplied function and RAW argument. Its existing
fold normalizes only the argument, with the unchanged fifth parameter. -/
def activeBranch (data : Data) : Program 5 :=
  .composition (InternalParameterizedCanonicalResultFold.actualJ data)
    ![.projection 1,.projection 2,.projection 4,.projection 3,.projection 0]

/-- Every off-activation input executes the COMPLETE original old vertex.
This is not an unrestricted identification of actualJ with a partial vertex. -/
def vertex (data : Data) (oldVertex : Program 5) : Program 5 :=
  InternalAcceptance.branch (activation data) oldVertex (activeBranch data)

def codomainMember (data : Data) : Program 5 :=
  .composition data.member ![.projection 2,.projection 0]

/-- A concrete local arithmetic invariant, not a path-acceptance premise.
Only the function coordinate changes along a path. Codomain membership and
argument typing remain at the identical parameter and original type codes. -/
def invariant (data : Data) : Program 5 :=
  InternalAcceptance.conjunction (activation data) (codomainMember data)

def Active (data : Data) (parameter domain codomain argument value : Nat) : Prop :=
  evaluate (selectedTyped data)
    (List.Vector.ofFn ![value,1 + Nat.pair domain codomain,parameter]) = 1 ∧
  evaluate (selectedTyped data) (List.Vector.ofFn ![argument,domain,parameter]) = 1

def activationGraph {α : Type} (data : Data)
    (out parameter domain codomain argument value : OTerm α) : Formula α :=
  programGraph (activation data) out
    (InternalApplicationPathMap.vertexArguments parameter domain codomain argument value)

def activationAccepted {α : Type} (data : Data)
    (parameter domain codomain argument value : OTerm α) : Formula α :=
  activationGraph data InternalOriginalStepGuard.one parameter domain codomain argument value

def activationFactors {α : Type} (data : Data)
    (parameter domain argument value arrow : OTerm α) : Formula α :=
  InternalParameterizedQuotientEdgeChecker.typedAccepted data value arrow parameter ⊓
    InternalParameterizedQuotientEdgeChecker.typedAccepted data argument domain parameter

def vertexGraph {α : Type} (data : Data) (oldVertex : Program 5)
    (out parameter domain codomain argument value : OTerm α) : Formula α :=
  programGraph (vertex data oldVertex) out
    (InternalApplicationPathMap.vertexArguments parameter domain codomain argument value)

def oldVertexGraph {α : Type} (oldVertex : Program 5)
    (out parameter domain codomain argument value : OTerm α) : Formula α :=
  programGraph oldVertex out
    (InternalApplicationPathMap.vertexArguments parameter domain codomain argument value)

def invariantAccepted {α : Type} (data : Data)
    (parameter domain codomain argument value : OTerm α) : Formula α :=
  programGraph (invariant data) InternalOriginalStepGuard.one
    (InternalApplicationPathMap.vertexArguments parameter domain codomain argument value)

def invariantFactors {α : Type} (data : Data)
    (parameter domain codomain argument value arrow : OTerm α) : Formula α :=
  activationFactors data parameter domain argument value arrow ⊓
    graph2 data.member InternalOriginalStepGuard.one codomain parameter

/-- The original source window and types are closed; Gamma's code remains
an arbitrary symbolic term. The already proved normalized membership slice
is sufficient to derive the invariant without a membership premise. -/
def initialPremises {α : Type} (context : Nat) (data : Data) (sigma tau : Ty)
    (parameter gammaCode argument value : OTerm α) : Formula α :=
  InternalOriginalUniformApplicationTyping.parameterGraph context parameter gammaCode ⊓
    (InternalParameterizedQuotientEdgeChecker.typedAccepted data value
      (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
      InternalParameterizedQuotientEdgeChecker.typedAccepted data argument
        (numeral (typeNumber sigma)) parameter)

def SelectedCalibrated (n : Nat) (arity : Fin n → Nat)
    (data : Data) (oldVertex : Program 5) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
    VertexCalibratedAt n arity symbols S Gamma table (vertex data oldVertex) ∧
      MapCalibratedAt n arity symbols S Gamma table (vertex data oldVertex)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPath
