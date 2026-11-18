import LogicLineages.PersistentMarking.DecisionObservations
namespace LogicLineages.PersistentMarking.DecisionObservationTargets
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations

def OccurrenceEnumeration : Prop := ∀ stack t locals q,
  (locals,q) ∈ occurrences stack t ↔ Occurs stack t locals q

def OccurrenceTyped : Prop := ∀ stack t τ locals q,
  Typed (BoundContext.prefix stack EmptyContext) t τ → Occurs stack t locals q →
  Typed (BoundContext.prefix locals EmptyContext) q q.type

def OccurrenceOrdinary : Prop := ∀ stack t locals q,
  Ordinary t → Occurs stack t locals q → Ordinary q

def OccurrenceValid : Prop := ∀ S stack t locals q,
  Valid S t → Occurs stack t locals q → Valid S q

def AssignmentEnumeration : Prop := ∀ V Γ stack vs,
  vs ∈ assignments V Γ stack ↔ Assignment V Γ stack vs

def AssignmentTyped : Prop := ∀ V Γ stack vs,
  Assignment V Γ stack vs → BaseTyped EmptyContext vs stack

def AssignmentLength : Prop := ∀ V Γ stack vs,
  Assignment V Γ stack vs → vs.length = stack.length

def OpeningTyped : Prop := ∀ V Γ stack vs q τ,
  Assignment V Γ stack vs → Typed (BoundContext.prefix stack EmptyContext) q τ →
  Typed EmptyContext (openOccurrence vs q) τ

def OpeningDepth : Prop := ∀ V Γ stack vs q,
  Assignment V Γ stack vs → lambdaDepth (openOccurrence vs q) = lambdaDepth q

def ObservationEnumeration : Prop := ∀ V B Γ t σ r,
  r ∈ observations V B Γ t σ ↔ Observation V B Γ t σ r

def ObservationPaper : Prop := ∀ S V B Γ t τ σ r,
  PaperTerm S t τ → Ordinary t → r ∈ observations V B Γ t σ →
  PaperTerm S r σ ∧ Ordinary r ∧ lambdaDepth r + used Γ ≤ B
end LogicLineages.PersistentMarking.DecisionObservationTargets
