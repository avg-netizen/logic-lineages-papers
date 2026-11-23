module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorOmegaMarkTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalConstructorLabelStratumTargets (FiniteMatrix finiteLabelBody finiteLabels)

/-- The physical raw Mark inputs are [finite label, ordinary owner, marked owner].
The source has tag 4 and two fields; the target has tag 5 and all five fields.
No numeral represents omega, and the finite label is supplied unshifted. -/
def onSlot (p : Program 1) (slot : Fin 3) : Program 3 := .composition p ![.projection slot]
def fieldAt (slot : Fin 3) (n : Nat) : Program 3 := onSlot (field n) slot
def markedType (decl : Program 1) : Program 3 := .composition decl ![fieldAt 1 0]
def markLabel : Program 3 := sameOf (.projection 0) (fieldAt 2 2)

def markGuards (fit decl : Program 1) : List (Program 3) :=
  [onSlot fit 1,onSlot fit 2,onSlot (nodeGood (literal 1 4) 2) 1,
    onSlot (nodeGood (literal 1 5) 5) 2,
    sameOf (fieldAt 1 0) (fieldAt 2 0),sameOf (markedType decl) (fieldAt 2 1),
    sameOf (fieldAt 1 1) (fieldAt 2 3),sameOf (constant 3 0) (fieldAt 2 4)]

def checkGuards : List (Program 3) → Program 3
  | [] => markLabel
  | h :: t => conjunction h (checkGuards t)

def markCase (fit decl : Program 1) : Program 3 := checkGuards (markGuards fit decl)

/-- The actual new local Mark arm and actual field-2 graph pay the
true syntactic finite universal at the same label. The declaration program
is a named physical input, not implicitly taken from the destination. -/
def ExactOpenOmegaMarkUse : Prop :=
  ∀ (fit decl : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (label source destination selected : OTerm α) (finite : FiniteMatrix α),
    Nonempty (Derivation B Γ (programGraph (markCase fit decl) (suc z) ![label,source,destination])) →
    Nonempty (Derivation B Γ (unary (field 2) selected destination)) →
    Nonempty (Derivation B Γ (finiteLabels finite)) →
    Nonempty (Derivation B Γ
      (eqn label selected ⊓ instantiate (finiteLabelBody finite) (emb selected)))

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorOmegaMarkTargets
