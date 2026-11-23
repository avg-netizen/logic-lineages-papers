module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOriginRowsFilterTargets (rowCell)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalOriginScanInductionTargets (Pools atRows goalAt)

def ExactOpenOriginScanInductionCons : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows row tail removed decoded rawL rawR scratchL scratchR joined outL outR : OTerm α),
    Pools B Γ removed decoded rawL rawR scratchL scratchR joined →
    D B Γ (rowCell rows row tail) → D B Γ (atRows r tail removed rawL rawR scratchL) →
    D B Γ (loopAccept r rows removed) →
    D B Γ (filterGraph true outL rows scratchL) →
    D B Γ (filterGraph false outR rows scratchL) →
    D B Γ (goalAt r rawL rawR outL outR)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsTargets
