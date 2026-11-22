module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (namedLeaves)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange)

/-- Actual sparse named leaf, independent of its standard scratch container. -/
def namedTerm {α : Type} (tag : Nat) (ty i : OTerm α) : OTerm α :=
  rawCons (numeral tag) (rawCons ty (rawCons i z))

/-- Input [index,grammar type]. -/
def namedCode (tag : Nat) : Program 2 :=
  binary fieldCons (literal 2 tag)
    (binary fieldCons (.projection 1)
      (binary fieldCons (.projection 0) (constantZero 2)))

def singletonLeaf (tag : Nat) : Program 2 := binary consCode (namedCode tag) (constantZero 2)

/-- Input [grammar type,ordered numeral scratch]. -/
def typeBlock (tag : Nat) : Program 2 := reorder (flatMap (singletonLeaf tag)) ![1,0]

/-- Input [ordered grammar types,ordered numeral scratch]. -/
def namedFromIds (tag : Nat) : Program 2 := flatMap (typeBlock tag)

/-- Actual numeral bound is inclusive: range gets the original M+1. -/
def boundSuccessor : Program 2 := .composition .succ (fun _ : Fin 1 => .projection 1)
def idsAt : Program 2 := .composition ascendingRange (fun _ : Fin 1 => boundSuccessor)

/-- Original free/bound branch, tag zero/one. Retains both ordered axes. -/
def namedAt (isBound : Bool) : Program 2 := binary (namedFromIds isBound.toNat) (.projection 0) idsAt

abbrev namedReport {α : Type} (isBound : Bool) (out K maxNumeral : OTerm α) :=
  programGraph (namedAt isBound) out ![K,maxNumeral]

def ExactCoverNamedLeavesValue : Prop :=
  ∀ (isBound : Bool) (K : List Nat) (M : Nat),
    evaluate (namedAt isBound) (numbersNumber K ::ᵥ M ::ᵥ nil) =
      numbersNumber (namedLeaves isBound.toNat K (List.range (M+1)))

/-- One forward, concrete cross-bound component. No prior leaf list or
transport is assumed: the original numeral and its weak lower and upper
bounds construct an actual occurrence in the larger physical named list. -/
def ExactOpenCoverNamedLeafAtLargerBound : Prop :=
  ∀ (isBound : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out K ty i m M : OTerm α),
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (ltF i (suc m))) →
    Nonempty (Derivation body Γ (ltF m (suc M))) →
    Nonempty (Derivation body Γ (namedReport isBound out K M)) →
    Nonempty (Derivation body Γ (memberGraph out (namedTerm isBound.toNat ty i)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
