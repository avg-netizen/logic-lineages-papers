module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

/-- Exact original ordered scratch decoding and membership for every
numeric input. Failed decoding and an empty pool both reject; a zero
candidate succeeds only at an actual occurrence of zero. -/
def ExactAllInputScratchMembership : Prop :=
  ∀ code candidate : Nat,
    evaluate scratchMember (code ::ᵥ candidate ::ᵥ nil) =
      ((decodeNumbers code).any (fun pool => pool.any (fun head => head == candidate))).toNat

def memberGraph {α : Type} (code candidate : OTerm α) : Formula α :=
  programGraph scratchMember (suc z) ![code,candidate]

/-- The same symbolic code/tape and selected candidate on both sides.
No externally decoded pool or numerical correctness is a premise. -/
def selectedOccurs {α : Type} (code selected : OTerm α) : Formula α :=
  (unary scratchMinimum (suc selected) code).imp (memberGraph code selected)

/-- Exact arbitrary-open internal occurrence, not an external membership
proof reflected into the calculus, and not an index/first-hit claim. -/
def ExactOpenScratchMinimumOccurs : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code selected : OTerm α),
    Nonempty (Derivation body Γ (selectedOccurs code selected))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
