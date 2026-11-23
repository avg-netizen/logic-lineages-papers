module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf succOf)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalConstructorLabelStratumTargets (FiniteMatrix finiteLabelBody)

/-- Actual Lower arm label test, inputs source finite label, target finite
label. Testing literal successor equality retains the nonzero check. -/
def lowerLabel : Program 2 := sameOf (.projection 0) (succOf (.projection 1))

def asField (i : Fin 2) (n : Nat) : Program 2 := .composition (field n) ![.projection i]

def markedShape (i : Fin 2) : Program 2 :=
  .composition (nodeGood (literal 1 5) 5) ![.projection i]

def preserved (n : Nat) : Program 2 := sameOf (asField 0 n) (asField 1 n)

def calledLowerLabel : Program 2 := .composition lowerLabel ![asField 0 2,asField 1 2]

/-- Literal local Lower checker on the original two tag-5 packed owner
rows (head,type,label,base,extras). The chosen fitted guard is physically
run at each original raw endpoint; no claim installs this in legacy r. -/
def lowerGuards (fit : Program 1) : List (Program 2) :=
  [.composition fit ![.projection 0],.composition fit ![.projection 1],
    markedShape 0,markedShape 1,preserved 0,preserved 1,preserved 3,preserved 4]

def checkGuards : List (Program 2) → Program 2
  | [] => calledLowerLabel
  | h :: t => ID1Completion.InternalAcceptance.conjunction h (checkGuards t)

def lowerCase (fit : Program 1) : Program 2 := checkGuards (lowerGuards fit)

def ExactNumericLowerLabel : Prop := ∀ src dst : Nat,
  evaluate lowerLabel (src ::ᵥ dst ::ᵥ nil) =
    (decide (src ≠ 0 ∧ src.pred = dst)).toNat

def ExactOpenLowerLabel : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (src dst : OTerm α),
    Nonempty (Derivation B Γ (programGraph lowerLabel (suc z) ![src,dst])) →
    Nonempty (Derivation B Γ (eqn src (suc dst) ⊓ ltF dst src))

/-- One actual accepted local Lower root, with its actual label field
reports, pays the genuine lower-label object hypothesis while preserving
the still-bound four later coordinates. -/
def ExactOpenLowerUse : Prop :=
  ∀ (fit : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (source destination src dst : OTerm α) (finite : FiniteMatrix α),
    Nonempty (Derivation B Γ (programGraph (lowerCase fit) (suc z) ![source,destination])) →
    Nonempty (Derivation B Γ (unary (field 2) src source)) →
    Nonempty (Derivation B Γ (unary (field 2) dst destination)) →
    Nonempty (Derivation B Γ (below (finiteLabelBody finite) src)) →
    Nonempty (Derivation B Γ (eqn src (suc dst) ⊓ instantiate (finiteLabelBody finite) (emb dst)))

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelTargets
