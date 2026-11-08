module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalParameterizedApplicationResultStack (liftP wireP)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [domain,codomain,source,target,argument,parameter]. The original
five-input numeric type guard ignores only the appended parameter. -/
def endpointTypeGuardP : Program 6 :=
  .composition InternalApplicationStepPeel.endpointTypeGuard
    ![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4]

def endpointGuardP (endpoint : Program 6) : Program 6 :=
  InternalAcceptance.conjunction endpointTypeGuardP endpoint

/-- All five original selectors inspect the unchanged raw edgeCode state;
the sixth endpoint coordinate is the unchanged separate parameter. -/
def endpointAtP (endpoint : Program 6) : Program 2 :=
  wireP (endpointGuardP endpoint)
    ![InternalApplicationStepPeel.domain,InternalApplicationStepPeel.codomain,
      InternalApplicationStepPeel.functionCode,InternalApplicationStepPeel.targetFunctionCode,
      InternalApplicationStepPeel.argumentCode]

def guardP (endpoint : Program 6) : Program 2 :=
  InternalAcceptance.conjunction (liftP InternalApplicationStepPeel.structuralGuard)
    (endpointAtP endpoint)

/-- Rejection returns the original raw state; acceptance returns the
original peeledState. No parameter field is inserted into the edge state. -/
def transitionP (endpoint : Program 6) : Program 2 :=
  InternalAcceptance.branch (guardP endpoint) (.projection 0)
    (liftP InternalApplicationStepPeel.peeledState)

/-- Raw-list recursion inputs are [head,tail result,initial state,parameter].
The head and initial state are ignored by this step; the parameter is carried
unchanged to the actual binary transition. -/
def repeatStepP (transition : Program 2) : Program 4 :=
  .composition transition ![.projection 1,.projection 3]

/-- Inputs [original raw-list code,initial state,parameter]. This is the
existing listRec at k=2. It has no numeric fuel or altered certificate codec. -/
def repeatP (transition : Program 2) : Program 3 :=
  InternalRawListRecursion.listRec (.projection (0 : Fin 2)) (repeatStepP transition)

/-- Iterate along the ORIGINAL raw certificate path, starting from the
whole original raw state, with the same separate parameter throughout. -/
def normalizerP (endpoint : Program 6) : Program 2 :=
  .composition (repeatP (transitionP endpoint))
    ![liftP InternalApplicationStepPeel.rawPath,.projection 0,.projection 1]

def selectedCheckerP (oldChecker : Program 4) : Program 2 :=
  wireP oldChecker ![source,target,step]

/-- The old checker sees all three original selectors of the entire
normalized raw state and then the SAME original parameter. -/
def checkedStateP (endpoint : Program 6) (oldChecker : Program 4) : Program 2 :=
  .composition (selectedCheckerP oldChecker) ![normalizerP endpoint,.projection 1]

def edgeStateP : Program 4 :=
  .composition edgeCode ![.projection 0,.projection 1,.projection 2]

/-- Inputs [source,target,step certificate,parameter]. Only the first three
coordinates form the original edgeCode state. The old checker is arbitrary. -/
def checkerP (endpoint : Program 6) (oldChecker : Program 4) : Program 4 :=
  .composition (checkedStateP endpoint oldChecker) ![edgeStateP,.projection 3]

def repeatGraph {α : Type} (transition : Program 2)
    (out code initial parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (repeatP transition) out code initial parameter

def endpointGraph {α : Type} (endpoint : Program 6)
    (out d e s t a parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph endpoint out ![d,e,s,t,a,parameter]

def transitionGraph {α : Type} (endpoint : Program 6)
    (out state parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (transitionP endpoint) out state parameter

def normalizerGraph {α : Type} (endpoint : Program 6)
    (out state parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (normalizerP endpoint) out state parameter

def checkerGraph {α : Type} (endpoint : Program 6) (oldChecker : Program 4)
    (out s t k parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (checkerP endpoint oldChecker) out s t k parameter

/-- Exactly the existing original arrow, outer tags, endpoint acceptance,
raw applications and stepLift graphs, with the sole parameter appended to
the endpoint graph. No normalization or checker-equivalence premise occurs. -/
def liftedCheckerPremises {α : Type} (endpoint : Program 6)
    (d e arrow s t a k sourceApp targetApp liftedStep parameter : OrdinaryArithmetic.Term α) :
    Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph1 InternalUnpair.left arrow s ⊓
      (graph1 InternalUnpair.left arrow t ⊓
        (graph1 InternalUnpair.left d a ⊓
          (endpointGraph endpoint InternalOriginalStepGuard.one d e s t a parameter ⊓
            (graph4 application sourceApp d e s a ⊓
              (graph4 application targetApp d e t a ⊓ graph1 stepLift liftedStep k))))))

/-- External calibration on the entire original five-input domain, at one
fixed arbitrary parameter slice. Source/argument retain universe decoding;
the target retains unrestricted packed decoding, exactly as before. -/
def EndpointCalibratedAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (endpoint : Program 6) (parameter : Nat) : Prop :=
  ∀ v : List.Vector Nat 5,
    evaluate endpoint (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,parameter]) =
      InternalApplicationStepPeel.endpointValue n arity symbols S Gamma v

def StepCalibratedAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (oldChecker : Program 4) (parameter : Nat) : Prop :=
  ∀ v : List.Vector Nat 3,
    evaluate oldChecker (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,parameter]) =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepChecker
