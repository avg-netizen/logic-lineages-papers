module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalProjectedCountBranchTargets (SideCountCongruence)
open NumberedWindowInternalProjectedCountInductionTargets (atRows project compared)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)

structure RowStepReports (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (code rawRow tail pool tailL tailR outL outR p pl pr joined : OTerm α) : Prop where
  input : D B Γ (consGraph code rawRow tail)
  priorL : D B Γ (filterGraph true tailL tail pool)
  priorR : D B Γ (filterGraph false tailR tail pool)
  stepL : D B Γ (programGraph (rowStep true) outL ![rawRow,tailL,pool])
  stepR : D B Γ (programGraph (rowStep false) outR ![rawRow,tailR,pool])
  projected : D B Γ (project p code)
  projectL : D B Γ (project pl outL)
  projectR : D B Γ (project pr outR)
  joinedProjected : D B Γ (appendGraph joined pl pr)
  tailLaw : D B Γ (atRows tail pool)

def ExactOpenProjectedCountRowStep : Prop :=
  SideCountCongruence true → SideCountCongruence false →
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (code rawRow tail pool tailL tailR outL outR p pl pr joined : OTerm α),
    RowStepReports B Γ code rawRow tail pool tailL tailR outL outR p pl pr joined →
    D B Γ (compared p joined)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepTargets
