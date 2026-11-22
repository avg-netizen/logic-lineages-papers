module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

abbrev accepts {α : Type} (base : Program 2) (V : Program 1) (a b : OTerm α) : Formula α :=
  programGraph (selected (step base V)) (suc z) ![a,b]

abbrev syntaxOne {α : Type} (V : Program 1) (a : OTerm α) : Formula α :=
  programGraph V (suc z) ![a]

/-- The selected physical exchange itself lifts. The source proof and
both parent syntax checks are actual object formulas under the same body. -/
def ExactOpenAuxMemoFunctionLift : Prop :=
  ∀ (base : Program 2) (V : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn fn' arg : OTerm α),
    let a := auxiliaryTerm dom cod fn arg
    let b := auxiliaryTerm dom cod fn' arg
    Nonempty (Derivation body Γ
      ((accepts base V fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)).imp (accepts base V a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
