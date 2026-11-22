module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Original ascending range. The old length is the actual next element,
including element zero; a standard scratch singleton is appended at right. -/
def singleton : Program 2 :=
  .composition consCode ![.projection 0,constantZero 2]

def rangeStep : Program 2 :=
  .composition append ![.projection 1,singleton]

def ascendingRange : Program 1 :=
  .recursion (constantZero 0) rangeStep

abbrev rangeReport {α : Type} (out bound : OTerm α) :=
  programGraph ascendingRange out ![bound]

/-- Actual ordered original list codec on every natural bound. -/
def ExactCoverAscendingRangeValue : Prop :=
  ∀ n : Nat, evaluate ascendingRange (n ::ᵥ nil) = numbersNumber (List.range n)

/-- Exact forward introduction at the actual reported range, below the
original exclusive bound. No inherited occurrence or backward claims. -/
def ExactOpenCoverAscendingRangeMember : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out bound i : OTerm α),
    Nonempty (Derivation body Γ (rangeReport out bound)) →
    Nonempty (Derivation body Γ (ltF i bound)) →
    Nonempty (Derivation body Γ (memberGraph out i))

def rangeOnFirst : Program 2 :=
  .composition ascendingRange (fun _ : Fin 1 => .projection 0)

def rangeMember : Program 2 :=
  .composition scratchMember ![rangeOnFirst,.projection 1]

abbrev rangeTest {α : Type} (bound i : OTerm α) : Formula α :=
  programGraph rangeMember (suc z) ![bound,i]

abbrev atBound {α : Type} (bound i : OTerm α) : Formula α :=
  (ltF i bound).imp (rangeTest bound i)

abbrev motive {α : Type} (i : OTerm α) : Formula (α ⊕ Fin 1) :=
  atBound (.var (.inr 0)) (i.relabel Sum.inl)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
