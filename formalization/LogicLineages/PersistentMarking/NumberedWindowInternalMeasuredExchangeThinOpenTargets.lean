module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

abbrev accepted {α : Type} (X : Program 2) (a b : OTerm α) : Formula α :=
  programGraph X (suc z) ![a,b]

/-- The parent's cover comparison and measure comparison are derived inside
the calculus. The two parent syntax reports are the only added premises. -/
def ExactOpenMeasuredFactoredAuxLift : Prop :=
  ∀ (s : Settings) (baseX : Program 2) (V baseM : Program 1) (P : Program 2) (G : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod fn fn' arg : OTerm α),
    let X := measuredFactoredExchange s baseX V baseM P G
    let a := auxiliaryTerm dom cod fn arg
    let b := auxiliaryTerm dom cod fn' arg
    Nonempty (Derivation body Γ
      ((accepted X fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)).imp (accepted X a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
