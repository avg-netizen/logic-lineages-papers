module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentation
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Finite original Program leaves only. The same validity and membership
leaves are shared literally by all wrappers. No proof or lift field is stored. -/
structure Data where
  validity : InternalOriginalStepGuard.Data
  member : Program 1
  oldEdge : InternalQuotientEdgeChecker.Data
  oldTyped : Program 2

/-- Every leaf is calibrated on ALL natural inputs at fixed Gamma and arbitrary
window S. Calibration is external evaluation equality, not an internal rule. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma data.validity ∧
    (InternalStructuralEndpointGuard.MembershipCalibrated S data.member ∧
      (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table data.oldEdge ∧
        InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma data.oldTyped))

/-- Literal membership of the supplied type coordinate, not of the value. -/
def membershipAt (member : Program 1) : Program 2 :=
  .composition member (fun _ : Fin 1 => .projection 1)

/-- The original canonical typed carrier, with its shared validity/raw-tag
wrapper, additionally exposes membership of the requested type in S. This
membership guard must be proved redundant on all original accepted inputs. -/
def typedChecker (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (oldTyped : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (membershipAt member)
    (InternalOriginalTypedCarrier.checker validity oldTyped)

def endpoint (data : Data) : Program 5 :=
  InternalStructuralEndpointGuard.endpoint data.validity data.member

/-- Guard outside the actual repeat-then-old-checker AST. It supplies the raw
validities needed by representative tag transport before any application lift. -/
def stepChecker (data : Data) : Program 3 :=
  InternalOriginalStepGuard.checker data.validity
    (InternalApplicationStepPeel.checker (endpoint data) data.oldEdge.stepProgram)

/-- The wrapped representatives retain exactly the selected guarded normalized
step AST. The target representative still uses packed validity only. -/
def edgeData (data : Data) : InternalQuotientEdgeChecker.Data :=
  InternalRepresentativeTag.withRepresentatives data.validity
    { stepProgram := stepChecker data,
      sourceRepresentative := data.oldEdge.sourceRepresentative,
      targetRepresentative := data.oldEdge.targetRepresentative }

def typed {α : Type} (data : Data) (value typ : OTerm α) : Formula α :=
  graph2 (typedChecker data.validity data.member data.oldTyped)
    InternalOriginalStepGuard.one value typ

/-- Exact external calibration of all constructed ASTs, including the final
quotient-edge checker on every natural endpoint/certificate triple. -/
def PresentationCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalApplicationStepPeel.EndpointCalibrated n arity symbols S Gamma (endpoint data) ∧
    (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table (edgeData data) ∧
      (InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma
        (typedChecker data.validity data.member data.oldTyped) ∧
        ∀ v : List.Vector Nat 3,
          evaluate (InternalQuotientEdgeChecker.checker (edgeData data)) v =
            (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
              (v.get 0) (v.get 1) (v.get 2)).toNat))

/-- Only canonical typed source, typed argument, actual certificate selectors
and accepted original quotient edge are assumed. In particular y is untyped. -/
def premises {α : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate s t k : OTerm α) : Formula α :=
  typed data x (numeral (typeNumber (.arrow sigma tau))) ⊓
    (typed data a (numeral (typeNumber sigma)) ⊓
      (selectors certificate s t k ⊓
        InternalQuotientEdgeChecker.accepted (edgeData data) x y certificate))

/-- The actual original arrow-constructor graph, endpoint acceptance and all
three raw outer-tag graphs are conclusions. No semantic decoded witness is
substituted for these arithmetic graph formulas. -/
def requirements {α : Type} (data : Data) (sigma tau : Ty)
    (s t a : OTerm α) : Formula α :=
  graph2 InternalListCodec.consCode (numeral (typeNumber (.arrow sigma tau)))
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) ⊓
    (InternalStructuralEndpointGuard.accepted data.validity data.member
      (numeral (typeNumber sigma)) (numeral (typeNumber tau)) s t a ⊓
      InternalStructuralEndpointGuard.tagGraphs
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) s t a)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentation
