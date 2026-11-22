module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowCoverAlgorithm (ordinary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedFromIds namedTerm)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- Generic two-field grammar layer, not a grammar recognizer. Inputs are
ordered outer keys and ordered inner keys, respectively; element fields
retain precisely that order. There is no numeral-range call. -/
abbrev taggedLayer (tag : Nat) : Program 2 := namedFromIds tag

abbrev taggedTerm {α : Type} (tag : Nat) (outer inner : OTerm α) :=
  namedTerm tag outer inner

abbrev taggedReport {α : Type} (tag : Nat) (out outer inner : OTerm α) : Formula α :=
  programGraph (taggedLayer tag) out ![outer,inner]

def ExactTaggedLayerValue (tag : Nat) : Prop :=
  ∀ (outer inner : List Nat),
    evaluate (taggedLayer tag) (numbersNumber outer ::ᵥ numbersNumber inner ::ᵥ nil) =
      numbersNumber (outer.flatMap fun x => inner.map fun y => packNode tag [x,y])

def ExactOpenTaggedLayerConstructor (tag : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out outer inner x y : OTerm α),
  Nonempty (Derivation body Γ (taggedReport tag out outer inner)) →
  Nonempty (Derivation body Γ (memberGraph outer x)) →
  Nonempty (Derivation body Γ (memberGraph inner y)) →
  Nonempty (Derivation body Γ (memberGraph out (taggedTerm tag x y)))

abbrev taggedOriginRow {α : Type} (tag : Nat) (outer inner key x y : OTerm α) : Formula α :=
  memberGraph outer x ⊓ (memberGraph inner y ⊓ eqn (taggedTerm tag x y) key)

abbrev taggedOriginMatrix {α : Type} (tag : Nat) (outer inner key : OTerm α) : Formula (α ⊕ Fin 2) :=
  taggedOriginRow tag (outer.relabel Sum.inl) (inner.relabel Sum.inl) (key.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

abbrev taggedOrigin {α : Type} (tag : Nat) (outer inner key : OTerm α) : Formula α :=
  block (taggedOriginMatrix tag outer inner key)

def ExactOpenTaggedLayerOrigin (tag : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out outer inner key : OTerm α),
  Nonempty (Derivation body Γ (taggedReport tag out outer inner)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (taggedOrigin tag outer inner key))

/-- The two actual reports share the same physical ordered outer list.
Only inner-list inclusion is required. -/
def ExactOpenTaggedLayerTransport (tag : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next outer inner inner' key : OTerm α),
  Nonempty (Derivation body Γ (taggedReport tag old outer inner)) →
  Nonempty (Derivation body Γ (taggedReport tag next outer inner')) →
  Nonempty (Derivation body Γ (axisInclusion inner inner')) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

/-- The unchanged ordinary branch: H heads outer, argument lists inner;
selected tag 4, original [head,args] sparse code, never tag 5. -/
abbrev ordinaryLayer := taggedLayer 4

abbrev ordinaryReport {α : Type} (out H args : OTerm α) : Formula α :=
  taggedReport 4 out H args

def ExactCoverOrdinaryLayerValue : Prop :=
  ∀ (H args : List Nat),
    evaluate ordinaryLayer (numbersNumber H ::ᵥ numbersNumber args ::ᵥ nil) =
      numbersNumber (ordinary H args)

def ExactOpenCoverOrdinaryLayerConstructor : Prop := ExactOpenTaggedLayerConstructor 4
def ExactOpenCoverOrdinaryLayerOrigin : Prop := ExactOpenTaggedLayerOrigin 4
def ExactOpenCoverOrdinaryLayerTransport : Prop := ExactOpenTaggedLayerTransport 4

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
