module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

abbrev paired (base : Program 2) (V : Program 1) : Program 2 :=
  pairedExchange (selected (step base V))

abbrev accepted {α : Type} (X : Program 2) (a b : OTerm α) : Formula α := programGraph X (suc z) ![a,b]

/-- Both true directions of the same physical exchange lift at one argument. -/
def ExactOpenPairedAuxMemoLift : Prop :=
  ∀ (base : Program 2) (V : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn fn' arg : OTerm α),
    let a := auxiliaryTerm dom cod fn arg
    let b := auxiliaryTerm dom cod fn' arg
    Nonempty (Derivation body Γ
      ((accepted (paired base V) fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)).imp
        (accepted (paired base V) a b)))

/-- The real cover comparison remains a condition on the original option
outputs of the two constructed parent seeds, in the same proof context. -/
def ExactOpenGuardedAuxMemoLift : Prop :=
  ∀ (C : Program 3) (s : Settings) (base : Program 2) (V : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn fn' arg outA outB : OTerm α),
    let a := auxiliaryTerm dom cod fn arg
    let b := auxiliaryTerm dom cod fn' arg
    let X := guardedExchange C s (paired base V)
    let parentCovers := unary (coverOption C s) outA a ⊓
      (unary (coverOption C s) outB b ⊓ eqn outA outB)
    Nonempty (Derivation body Γ
      ((accepted X fn fn' ⊓ ((syntaxOne V a ⊓ syntaxOne V b) ⊓ parentCovers)).imp
        (accepted X a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedTargets
