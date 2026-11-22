module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)

/-- Exactly the original termParts tag and field-count patterns. -/
def layout : List (Nat × Nat) := [(0,2),(1,2),(2,2),(3,1),(4,2),(5,5),(6,4)]

def header (tag arity : Nat) : Program 1 := nodeGood (literal 1 tag) arity

def headerAny : List (Nat × Nat) → Program 1
  | [] => constantZero 1
  | (tag,arity) :: rest => branch (normalize (header tag arity)) (headerAny rest) (constantOne 1)

def headerAt {α : Type} (tag arity : Nat) (q : OTerm α) : Formula α :=
  unary (header tag arity) (suc z) q

/-- Actual object disjunction. Empty branch is unreachable at output
one: it would equate successor zero and zero. -/
def headersAt {α : Type} : List (Nat × Nat) → OTerm α → Formula α
  | [], _ => eqn (suc z) z
  | (tag,arity) :: rest, q => headerAt tag arity q ⊔ headersAt rest q

/-- A physically reselected guard, not a proof-tree reflection theorem
for arbitrary V with the same natural evaluator. -/
def selectedValidity (V : Program 1) : Program 1 := conjunction V (headerAny layout)

def ExactCoverSelectedValidityCalibration : Prop :=
  ∀ V : Program 1, TermSyntaxCalibrated V → TermSyntaxCalibrated (selectedValidity V)

def ExactOpenCoverSelectedValidityHeaders : Prop :=
  ∀ (V : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation body Γ (unary (selectedValidity V) (suc z) q)) →
    Nonempty (Derivation body Γ (unary V (suc z) q ⊓ headersAt layout q))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
