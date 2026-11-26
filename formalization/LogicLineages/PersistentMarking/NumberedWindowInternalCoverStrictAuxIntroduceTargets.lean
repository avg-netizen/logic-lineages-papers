module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph contextTable contextStep)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxChildren)

/-- Introduction at one literal original aux parent. Both genuine
windows must already inhabit this same physically selected memo. -/
def ExactOpenCoverStrictAuxIntroduceRow : Prop :=
  ∀ (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fn arg old : OTerm α),
    Nonempty (Derivation body Γ (strictAuxChildren B T ctx dom cod fn arg)) →
    Nonempty (Derivation body Γ (contextTable (strictAuxUpdate B T) old (memoPrior dom cod fn arg) ctx)) →
    Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate B T) (suc cod) (memoPrior dom cod fn arg) old ctx))

def ExactOpenCoverStrictAuxIntroduce : Prop :=
  ∀ (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ (strictAuxChildren B T ctx dom cod fn arg)) →
    Nonempty (Derivation body Γ (windowGraph (strictAuxWindow B T) ctx cod (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
