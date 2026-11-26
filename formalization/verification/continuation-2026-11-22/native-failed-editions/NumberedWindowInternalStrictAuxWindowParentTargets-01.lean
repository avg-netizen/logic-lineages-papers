module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets

/-- The actual new packed parent query at the literal original tag-six key
supplies both actual same-context child queries. No physical table or update
report is supplied by the caller. -/
def ExactOpenStrictAuxWindowParent : Prop :=
  ∀ (base : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ
      (windowGraph (strictAuxWindow base T) ctx cod (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (strictAuxChildren base T ctx dom cod fn arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets
