module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalPairedPackedLeastChecks
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinUncoveredCountBoundProof (exact_PhysicalUncoveredCountBound)
open NumberedWindowInternalThinUncoveredCountCompareProof (internalStrictDecrease)
open NumberedWindowInternalThinPairedPackedLeastProof

theorem exact_OriginalPhysicalCountLength : CountLengthBound :=
  exact_PhysicalUncoveredCountBound

theorem exact_OriginalPhysicalCountStrict : InternalStrictDecrease :=
  internalStrictDecrease

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- For two actual successful original packed least calls at a genuine
guarded paired edge, the original arithmetic calculus proves their outputs
equal. All finite-count and closure premises are discharged here. -/
theorem exact_OpenOriginalPairedPackedLeast (C : Program 3) (base : Program 2) (W : Program 3)
    (s : Settings) (ctx ty a b x y : OTerm α) :
    let X := guardedExchange C s (pairedExchange base)
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty a x)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty b y)) →
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx ty a b)) →
    Nonempty (Derivation B Γ (eqn x y)) :=
  exact_OpenThinPairedPackedLeast exact_OriginalPhysicalCountLength exact_OriginalPhysicalCountStrict C base W s
    ctx ty a b x y

#print axioms exact_OriginalPhysicalCountLength
#print axioms exact_OriginalPhysicalCountStrict
#print axioms exact_OpenOriginalPairedPackedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalPairedPackedLeastChecks
