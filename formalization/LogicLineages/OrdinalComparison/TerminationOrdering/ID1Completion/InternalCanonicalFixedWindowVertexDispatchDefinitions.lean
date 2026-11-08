module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatch
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Reuse the SAME canonical descent leaves, without correctness, fixedness,
typed-output, path-invariant or application-lift fields. -/
abbrev Data := InternalCanonicalDescentSelection.Data

/-- A finite constant AST built only from the original Program constructors.
The selected window is not an ambient Gamma code or a new runtime input. -/
def constant (n : Nat) : Nat → Program n
  | 0 => InternalAcceptance.constantZero n
  | k + 1 => .composition .succ (fun _ : Fin 1 => constant n k)

/-- The original successor-of-pair arrow constructor on every natural pair. -/
def arrowCode (domain codomain : Nat) : Nat := 1 + Nat.pair domain codomain

/-- This is exactly the canonical descent typed AST: member, V, original
left tag and T-fixedness. No old typed, H or N-fixed conjunct is inserted. -/
def typedChecker (data : Data) : Program 2 :=
  InternalCanonicalDescentSelection.selectedTyped data

/-- All five coordinates are [context,domain,codomain,argument,value]. -/
def functionTyped (data : Data) : Program 5 :=
  .composition (typedChecker data)
    ![.projection 4,consOf (.projection 1) (.projection 2)]

def argumentTyped (data : Data) : Program 5 :=
  .composition (typedChecker data) ![.projection 3,.projection 1]

/-- Selection substitutes contextCode symbols S table for window. The two
typed tests are the same canonical typed Program, with exact-one acceptance. -/
def activation (window : Nat) (data : Data) : Program 5 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (.projection 0) (constant 5 window))
    (InternalAcceptance.conjunction (functionTyped data) (argumentTyped data))

/-- Literal actualJ at [domain,codomain,value,RAW argument]. actualJ computes
C(domain,codomain,value,N(argument)); the function is not normalized again. -/
def activeBranch (data : Data) : Program 5 :=
  .composition (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
    ![.projection 1,.projection 2,.projection 4,.projection 3]

/-- The inactive branch is the COMPLETE original five-input vertex, with
all inputs unchanged. It is not a new zero or source-filtered default. -/
def vertex (window : Nat) (data : Data) (oldVertex : Program 5) : Program 5 :=
  InternalAcceptance.branch (activation window data) oldVertex (activeBranch data)

def Active (window : Nat) (data : Data)
    (context domain codomain argument value : Nat) : Prop :=
  context = window ∧
    (evaluate (typedChecker data) (List.Vector.ofFn ![value,arrowCode domain codomain]) = 1 ∧
      evaluate (typedChecker data) (List.Vector.ofFn ![argument,domain]) = 1)

def activationAccepted {α : Type} (window : Nat) (data : Data)
    (context domain codomain argument value : OTerm α) : Formula α :=
  programGraph (activation window data) InternalOriginalStepGuard.one
    (InternalApplicationPathMap.vertexArguments context domain codomain argument value)

/-- The original arrow constructor graph supplies arrow separately. These
are actual canonical typed graphs, not externally reflected typing facts. -/
def activationFactors {α : Type} (window : Nat) (data : Data)
    (context domain argument value arrow : OTerm α) : Formula α :=
  InternalControlGraph.equal context (numeral window) ⊓
    (InternalCanonicalQuotientEdgeSelection.typedAccepted data value arrow ⊓
      InternalCanonicalQuotientEdgeSelection.typedAccepted data argument domain)

def vertexGraph {α : Type} (window : Nat) (data : Data) (oldVertex : Program 5)
    (out context domain codomain argument value : OTerm α) : Formula α :=
  programGraph (vertex window data oldVertex) out
    (InternalApplicationPathMap.vertexArguments context domain codomain argument value)

/-- Exact actualJ graph, retaining its internal N(argument) computation.
No graph equality with C(domain,codomain,value,argument) is asserted. -/
def applicationGraph {α : Type} (data : Data)
    (out domain codomain value argument : OTerm α) : Formula α :=
  InternalCanonicalQuotientEdgeApplicationLift.applicationGraph data
    out domain codomain value argument

/-- The invariant's two typed tests use fixed ORIGINAL closed type codes. -/
def closedFunctionTyped (data : Data) (sigma tau : Ty) : Program 5 :=
  .composition (typedChecker data)
    ![.projection 4,constant 5 (typeNumber (.arrow sigma tau))]

def closedArgumentTyped (data : Data) (sigma : Ty) : Program 5 :=
  .composition (typedChecker data) ![.projection 3,constant 5 (typeNumber sigma)]

/-- A concrete arithmetic path invariant. The context, domain, codomain and
argument coordinates do not move along a path; only the function value does.
This is neither a path checker nor a computability predicate. -/
def invariant (window : Nat) (data : Data) (sigma tau : Ty) : Program 5 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (.projection 0) (constant 5 window))
    (InternalAcceptance.conjunction
      (InternalApplicationStepPeel.same (.projection 1) (constant 5 (typeNumber sigma)))
      (InternalAcceptance.conjunction
        (InternalApplicationStepPeel.same (.projection 2) (constant 5 (typeNumber tau)))
        (InternalAcceptance.conjunction
          (closedFunctionTyped data sigma tau) (closedArgumentTyped data sigma))))

def invariantAccepted {α : Type} (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument value : OTerm α) : Formula α :=
  programGraph (invariant window data sigma tau) InternalOriginalStepGuard.one
    (InternalApplicationPathMap.vertexArguments context domain codomain argument value)

def invariantFactors {α : Type} (window : Nat) (data : Data) (sigma tau : Ty)
    (context domain codomain argument value : OTerm α) : Formula α :=
  InternalControlGraph.equal context (numeral window) ⊓
    (InternalControlGraph.equal domain (numeral (typeNumber sigma)) ⊓
      (InternalControlGraph.equal codomain (numeral (typeNumber tau)) ⊓
        (InternalCanonicalQuotientEdgeSelection.typedAccepted data value
            (numeral (typeNumber (.arrow sigma tau))) ⊓
          InternalCanonicalQuotientEdgeSelection.typedAccepted data argument
            (numeral (typeNumber sigma)))))

/-- Properties of one fixed selection, never Data fields or supplied laws.
All graph statements retain arbitrary derivation contexts and symbolic terms. -/
def InternalLaws (window : Nat) (data : Data) (oldVertex : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
    (∀ (context domain codomain argument value arrow : OTerm α),
      Nonempty (Derivation body Delta
        ((graph2 InternalListCodec.consCode arrow domain codomain).imp
          ((activationAccepted window data context domain codomain argument value).iff
            (activationFactors window data context domain argument value arrow))))) ∧
    ((∀ (context domain codomain argument value out : OTerm α),
      Nonempty (Derivation body Delta
        ((activationAccepted window data context domain codomain argument value).imp
          ((vertexGraph window data oldVertex out context domain codomain argument value).iff
            (applicationGraph data out domain codomain value argument))))) ∧
      ∀ (sigma tau : Ty) (context domain codomain argument value : OTerm α),
        Nonempty (Derivation body Delta
          ((invariantAccepted window data sigma tau context domain codomain argument value).iff
            (invariantFactors window data sigma tau context domain codomain argument value))) ∧
        Nonempty (Derivation body Delta
          ((invariantAccepted window data sigma tau context domain codomain argument value).imp
            (activationAccepted window data context domain codomain argument value))))

/-- The SAME selected canonical Edge is used by the existing path API.
There is deliberately no EdgeCompatibility or path-preservation field. -/
def InvariantLaws (window : Nat) (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty),
    InternalApplicationPathLift.InvariantPreservation body
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
      (invariant window data sigma tau)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatch
