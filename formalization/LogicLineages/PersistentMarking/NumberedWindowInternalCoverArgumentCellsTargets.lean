module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (cells)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)

/-- Singleton scratch block for input [old arguments, term]. Only the
element uses the shifted sparse polynomial pair. -/
def cellSingle : Program 2 :=
  binary consCode (reorder fieldCons ![1,0]) (constantZero 2)

/-- For input [term, ordered arguments], get that term's ordered row. -/
def cellBlock : Program 2 := reorder (flatMap cellSingle) ![1,0]

/-- For input [ordered terms, ordered arguments], flatten in that order. -/
def cellsTail : Program 2 := flatMap cellBlock

/-- The leading zero is an actual scratch cons, even if either axis is empty. -/
def cellsAt : Program 2 := binary consCode (constantZero 2) cellsTail

abbrev cellsReport {α : Type} (out terms args : OTerm α) : Formula α :=
  programGraph cellsAt out ![terms,args]

def ExactCoverArgumentCellsValue : Prop :=
  ∀ (terms args : List Nat),
    evaluate cellsAt (numbersNumber terms ::ᵥ numbersNumber args ::ᵥ nil) = numbersNumber (cells terms args)

def ExactOpenCoverArgumentCellsConstructor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out terms args q a : OTerm α),
  Nonempty (Derivation body Γ (cellsReport out terms args)) →
  Nonempty (Derivation body Γ (memberGraph out z)) ∧
    (Nonempty (Derivation body Γ (memberGraph terms q)) →
     Nonempty (Derivation body Γ (memberGraph args a)) →
     Nonempty (Derivation body Γ (memberGraph out (rawCons q a))))

abbrev cellOriginRow {α : Type} (terms args key q a : OTerm α) : Formula α :=
  memberGraph terms q ⊓ (memberGraph args a ⊓ eqn (rawCons q a) key)

abbrev cellOriginMatrix {α : Type} (terms args key : OTerm α) : Formula (α ⊕ Fin 2) :=
  cellOriginRow (terms.relabel Sum.inl) (args.relabel Sum.inl) (key.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

abbrev cellPairOrigin {α : Type} (terms args key : OTerm α) : Formula α :=
  block (cellOriginMatrix terms args key)

abbrev cellOrigin {α : Type} (terms args key : OTerm α) : Formula α :=
  eqn z key ⊔ cellPairOrigin terms args key

def ExactOpenCoverArgumentCellsOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out terms args key : OTerm α),
  Nonempty (Derivation body Γ (cellsReport out terms args)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (cellOrigin terms args key))

/-- The sole two premises needed by the transport of cells are *object*
membership inclusions between their respective input axes. -/
abbrev axisInclusion {α : Type} (old next : OTerm α) : Formula α :=
  allOne ((memberGraph (old.relabel Sum.inl) (.var (.inr 0))).imp
    (memberGraph (next.relabel Sum.inl) (.var (.inr 0))))

def ExactOpenCoverArgumentCellsTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out next terms terms' args args' key : OTerm α),
  Nonempty (Derivation body Γ (cellsReport out terms args)) →
  Nonempty (Derivation body Γ (cellsReport next terms' args')) →
  Nonempty (Derivation body Γ (axisInclusion terms terms')) →
  Nonempty (Derivation body Γ (axisInclusion args args')) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
