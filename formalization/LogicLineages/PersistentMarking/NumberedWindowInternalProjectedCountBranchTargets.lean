module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets (atRows project compared)

def sidedAppend {α : Type} (side : Bool) (out retained idle : OTerm α) : Formula α :=
  if side then appendGraph out retained idle else appendGraph out idle retained

/-- A small arithmetic interface for the denotation-free cons step.
Separate exact proofs supply its two Bool cases. -/
def SideCountCongruence (side : Bool) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (target oldTail retainedTail idle old retained joinedTail joined : OTerm α),
    D B Γ (consGraph old target oldTail) →
    D B Γ (consGraph retained target retainedTail) →
    D B Γ (sidedAppend side joinedTail retainedTail idle) →
    D B Γ (sidedAppend side joined retained idle) →
    D B Γ (compared oldTail joinedTail) →
    D B Γ (compared old joined)

structure SelectedBranch (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (side : Bool)
    (code rawRow tail pool vt vi vc idle allOut chosenOut idleOut joined : OTerm α) : Prop where
  inputCell : D B Γ (consGraph code rawRow tail)
  retained : D B Γ (consGraph vc rawRow vt)
  skipped : D B Γ (eqn idle vi)
  tailChosen : D B Γ (filterGraph side vt tail pool)
  tailIdle : D B Γ (filterGraph (!side) vi tail pool)
  projected : D B Γ (project allOut code)
  chosenProjected : D B Γ (project chosenOut vc)
  idleProjected : D B Γ (project idleOut idle)
  joinedProjected : D B Γ (sidedAppend side joined chosenOut idleOut)
  tailLaw : D B Γ (atRows tail pool)

def ExactOpenProjectedCountBranch : Prop :=
  ∀ (side : Bool), SideCountCongruence side →
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code rawRow tail pool vt vi vc idle allOut chosenOut idleOut joined : OTerm α),
    SelectedBranch B Γ side code rawRow tail pool vt vi vc idle allOut chosenOut idleOut joined →
    D B Γ (compared allOut joined)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchTargets
