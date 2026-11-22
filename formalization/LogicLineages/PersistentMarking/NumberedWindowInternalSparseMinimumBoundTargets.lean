module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open SourceComputabilityFormulaSupportProof (existsOne)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def boundedRow {α : Type} (code candidate minimum : OTerm α) : Formula α :=
  unary scratchMinimum (suc minimum) code ⊓ (strictLess candidate minimum).not

def boundedWitness {α : Type} (code candidate : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (boundedRow (code.relabel j) (candidate.relabel j) (.var (.inr 0)))

/-- Every genuine scratch-list member supplies a successful minimum with
an original internal order bound at that same open candidate. -/
def ExactOpenMemberHasBoundedMinimum : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code candidate : OTerm α),
    Nonempty (Derivation body Γ ((memberGraph code candidate).imp (boundedWitness code candidate)))

/-- A member cannot be strictly smaller than the actual returned minimum.
The input list and both compared terms are arbitrary open object terms. -/
def ExactOpenScratchMinimumLowerBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code candidate minimum : OTerm α),
    Nonempty (Derivation body Γ
      ((unary scratchMinimum (suc minimum) code ⊓ memberGraph code candidate).imp
        (strictLess candidate minimum).not))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundTargets
