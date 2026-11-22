module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

abbrev measureGraph {α : Type} (base : Program 1) (combine : Program 2) (out raw : OTerm α) : Formula α :=
  programGraph (selectedMeasure (measureUpdate base combine)) out ![raw]

/-- The genuine selected measure at the original constructed auxiliary parent. -/
def ExactOpenAuxMeasureEvaluation : Prop :=
  ∀ (base : Program 1) (combine : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn arg mf ma out : OTerm α),
    let children := measureGraph base combine mf fn ⊓ measureGraph base combine ma arg
    let emit := programGraph combine out ![mf,ma]
    Nonempty (Derivation body Γ ((children ⊓ emit).imp
      (measureGraph base combine out (auxiliaryTerm dom cod fn arg))))

/-- Actual equality of the two parent measures follows from one common
function output value. The argument is literally identical, and all reports
use the same selected physical measure. -/
def ExactOpenAuxMeasureEquality : Prop :=
  ∀ (base : Program 1) (combine : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (dom cod fn fn' arg m x y : OTerm α),
    let children := measureGraph base combine m fn ⊓ measureGraph base combine m fn'
    let parents := measureGraph base combine x (auxiliaryTerm dom cod fn arg) ⊓
      measureGraph base combine y (auxiliaryTerm dom cod fn' arg)
    Nonempty (Derivation body Γ ((children ⊓ parents).imp (eqn x y)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
