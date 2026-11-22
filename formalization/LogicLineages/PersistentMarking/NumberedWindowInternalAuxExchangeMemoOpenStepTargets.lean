module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePair (pairTerm)

/-- An actual successful auxiliary row at the original predecessor key.
The table lookup is a real derivation at the same gap and prior table. -/
def ExactOpenAuxMemoStepAtGap : Prop :=
  ∀ (base : Program 2) (V : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn fn' arg gap old : OTerm α),
    let src := auxiliaryTerm dom cod fn arg
    let dst := auxiliaryTerm dom cod fn' arg
    let prior := OrdinaryArithmetic.addTerm (pairTerm fn fn') gap
    Nonempty (Derivation body Γ (eqn (suc prior) (pairTerm src dst))) →
    Nonempty (Derivation body Γ (programGraph V (suc z) ![src])) →
    Nonempty (Derivation body Γ (programGraph V (suc z) ![dst])) →
    Nonempty (Derivation body Γ (programGraph lookup (suc z) ![gap,old])) →
    Nonempty (Derivation body Γ (programGraph (step base V) (suc z) ![prior,old,z,z]))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepTargets
