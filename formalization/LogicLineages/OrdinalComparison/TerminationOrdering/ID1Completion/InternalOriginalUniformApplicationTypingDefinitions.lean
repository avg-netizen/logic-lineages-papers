module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTyping
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)

/-- The original parameter pairing is an actual graph. Its second coordinate
is a symbolic arithmetic term, with no decoded ambient-context premise. -/
def parameterGraph {α : Type} (context : Nat)
    (parameter gammaCode : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalPairing.pairing parameter (numeral context) gammaCode

def memberGraph {α : Type} (data : Data)
    (out typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 data.member out typ parameter

/-- The existing ternary canonical typed checker, including source validity,
the original outer tag, and fixedness of the same actual transition. -/
def typedGraph {α : Type} (data : Data)
    (value typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (InternalOriginalUniformDescentSelection.selectedTyped data)
    InternalOriginalStepGuard.one value typ parameter

/-- The unchanged actualJ receives the supplied function directly and
normalizes only its argument. All types and the parameter remain symbolic;
codomain membership is an explicit premise of this generic arithmetic rule. -/
def applicationPremises {α : Type} (data : Data)
    (arrow domain codomain function argument out parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow domain codomain ⊓
    (memberGraph data InternalOriginalStepGuard.one codomain parameter ⊓
      (typedGraph data function arrow parameter ⊓
        (typedGraph data argument domain parameter ⊓
          InternalParameterizedCanonicalResultFold.applicationGraph
            data out domain codomain function argument parameter)))

/-- Closed original source types and a literal parameter-pair graph replace
the generic membership premise. The function, argument, output, parameter
and Gamma code are still arbitrary arithmetic terms. -/
def runtimePremises {α : Type} (context : Nat) (data : Data) (sigma tau : Ty)
    (parameter gammaCode function argument out : OrdinaryArithmetic.Term α) : Formula α :=
  parameterGraph context parameter gammaCode ⊓
    (typedGraph data function (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
      (typedGraph data argument (numeral (typeNumber sigma)) parameter ⊓
        InternalParameterizedCanonicalResultFold.applicationGraph data out
          (numeral (typeNumber sigma)) (numeral (typeNumber tau)) function argument parameter))

/-- One unchanged Data precedes every source window and every symbolic
runtime Gamma code. No codomain membership or function-normalization
fixedness premise occurs in this application-typing law. -/
def UniformApplicationLaw (n : Nat) (data : Data) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode function argument out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      data sigma tau parameter gammaCode function argument out).imp
      (typedGraph data out (numeral (typeNumber tau)) parameter)))

/-- Retain the existing normalized tuple's global calibration, both complete
internal law packages, symbolic membership slice, and all original descent,
typed, canonical-fold and whole-state-success calibrations. -/
def RetainedNormalizedPackage (n : Nat) (arity : Fin n → Nat) (data : Data) : Prop :=
  InternalOriginalUniformDescentSelection.Calibrated n arity (normalizeData data) ∧
    InternalOriginalUniformDescentSelection.InternalLaws (normalizeData data) ∧
    InternalParameterizedCanonicalResultFold.InternalLaws (normalizeData data) ∧
    InternalOriginalUniformContextMembership.SliceLaw data.member ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
      SubtypeClosed (fun typ => typ ∈ S) →
      InternalOriginalUniformCanonicalResultFold.SelectedCalibrated
        n arity symbols S Gamma table (normalizeData data)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTyping
