module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuard
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal membership of the ORIGINAL decoded codomain in the fixed window.
The original type decoder is total, but its definition is not replaced here. -/
def membershipValue (S : List Ty) (value : Nat) : Nat :=
  match NumberedNumericDecoding.decodeType value with
  | some tau => (decide (tau ∈ S)).toNat
  | none => 0

/-- One unary leaf, calibrated on every natural code. This is external
evaluation calibration, not an object-language membership inference rule. -/
def MembershipCalibrated (S : List Ty) (member : Program 1) : Prop :=
  ∀ v : List.Vector Nat 1, evaluate member v = membershipValue S (v.get 0)

/-- Every leaf keeps the coordinate order [domain,codomain,source,target,argument].
Source and argument literally reuse the same unary sourceValid Program. -/
def sourceAt (validity : InternalOriginalStepGuard.Data) : Program 5 :=
  .composition validity.sourceValid (fun _ : Fin 1 => .projection 2)

def targetAt (validity : InternalOriginalStepGuard.Data) : Program 5 :=
  .composition validity.targetValid (fun _ : Fin 1 => .projection 3)

def argumentAt (validity : InternalOriginalStepGuard.Data) : Program 5 :=
  .composition validity.sourceValid (fun _ : Fin 1 => .projection 4)

def membershipAt (member : Program 1) : Program 5 :=
  .composition member (fun _ : Fin 1 => .projection 1)

/-- A concrete seven-test endpoint AST: source-universe, packed target,
argument-universe, the three ORIGINAL raw outer-tag equalities and codomain
membership. endpointTypeGuard literally uses consCode for the arrow code.
All conjunctions test exactly one, and every rejected input returns zero. -/
def endpoint (validity : InternalOriginalStepGuard.Data) (member : Program 1) : Program 5 :=
  InternalAcceptance.conjunction (sourceAt validity)
    (InternalAcceptance.conjunction (targetAt validity)
      (InternalAcceptance.conjunction (argumentAt validity)
        (InternalAcceptance.conjunction InternalApplicationStepPeel.endpointTypeGuard
          (membershipAt member))))

def accepted {α : Type} (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (d e s t a : OTerm α) : Formula α :=
  InternalApplicationStepPeel.graph5 (endpoint validity member)
    InternalOriginalStepGuard.one d e s t a

/-- Actual original unpair-left graphs, rather than semantic decoded types.
The arrow is a symbolic output of the original consCode graph in the target. -/
def tagGraphs {α : Type} (arrow d s t a : OTerm α) : Formula α :=
  graph1 InternalUnpair.left arrow s ⊓
    (graph1 InternalUnpair.left arrow t ⊓ graph1 InternalUnpair.left d a)

/-- No graph here is supplied by semantic truth or external calibration.
In the forward factorization these seven accepted graphs are conclusions. -/
def requirements {α : Type} (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (arrow d e s t a : OTerm α) : Formula α :=
  graph1 validity.sourceValid InternalOriginalStepGuard.one s ⊓
    (graph1 validity.targetValid InternalOriginalStepGuard.one t ⊓
      (graph1 validity.sourceValid InternalOriginalStepGuard.one a ⊓
        (tagGraphs arrow d s t a ⊓ graph1 member InternalOriginalStepGuard.one e)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuard
