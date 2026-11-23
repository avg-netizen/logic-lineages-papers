module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (applyUnary exactBody run)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowAtomicPositiveTargets (bottomAddress)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

def recognize : Program 1 :=
  conjunction (exactBody 1) (applyUnary bottomSource cellHead)

def packedSingletonBottom {α : Type} (ctx t : OrdinaryArithmetic.Term α) :
    OrdinaryArithmetic.Term α :=
  rawCons (packedBottomTerm ctx t) OrdinaryArithmetic.zeroTerm

def ExactNumericSingletonBottom : Prop :=
  ∀ x, run recognize x = 1 ↔ ∃ ctx t, x = pack [bottomAddress ctx t]

def ExactOpenSingletonBottom : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx t : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (programGraph recognize
      (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![packedSingletonBottom ctx t]))

/-- Numerical safety of rejecting nonempty targets in the visible branch.
The supplied direct certificate remains arbitrary. -/
def ExactDirectSingletonBottomTarget : Prop :=
  ∀ (xs : Entries) (s : Settings) (ctx t w y : Nat),
    NumberedWindowConcreteCheckers.direct xs s (pack [bottomAddress ctx t]) w y = true →
    y = 0

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomTargets
