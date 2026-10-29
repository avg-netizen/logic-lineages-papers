module

public import LogicLineages.RL.Targets
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.RL

theorem faithful_comp {F G H : Framework}
    (first : Transformation F G) (second : Transformation G H) :
    Faithful F H (second.agentMap ∘ first.agentMap)
      (first.environmentMap ∘ second.environmentMap) := by
  intro a b e
  exact (second.faithful (first.agentMap a) (first.agentMap b) e).trans
    (first.faithful a b (second.environmentMap e))

namespace FiniteExample

abbrev source : Framework where
  Agent := Fin 2
  Environment := Fin 2
  value a e := if a.val = 1 ∧ e.val = 0 then 1 else 0

abbrev middle : Framework where
  Agent := Fin 3
  Environment := Fin 3
  value a e := if a.val = 0 then 0 else
    if a.val = 1 then (if e.val = 0 then 1 else 0) else (if e.val = 1 then 1 else 2)

abbrev destination : Framework where
  Agent := Fin 3
  Environment := Fin 2
  value a e := if a.val = 2 then (if e.val = 0 then 1 else 2) else 0

def firstAgents : source.Agent → middle.Agent :=
  fun a => ⟨a.val, Nat.lt_trans a.isLt (by decide : 2 < 3)⟩
def firstEnvironments : middle.Environment → source.Environment :=
  fun e => if e.val = 0 then 0 else 1
def secondAgents : middle.Agent → destination.Agent := fun a => a
def secondEnvironments : destination.Environment → middle.Environment :=
  fun e => if e.val = 0 then 1 else 2

def first : Transformation source middle where
  agentMap := firstAgents
  environmentMap := firstEnvironments
  faithful := by
    intro a b e
    fin_cases a <;> fin_cases b <;> fin_cases e <;>
      norm_num [firstAgents, firstEnvironments, source, middle]
  agentsSeparated := by
    refine ⟨0, 1, 0, ?_⟩
    norm_num [firstAgents, source, middle]
  environmentVaries := by
    refine ⟨1, 1, 0, ?_⟩
    norm_num [firstAgents, source, middle]

def second : Transformation middle destination where
  agentMap := secondAgents
  environmentMap := secondEnvironments
  faithful := by
    intro a b e
    fin_cases a <;> fin_cases b <;> fin_cases e <;>
      norm_num [secondAgents, secondEnvironments, middle, destination]
  agentsSeparated := by
    refine ⟨0, 2, 0, ?_⟩
    norm_num [secondAgents, middle, destination]
  environmentVaries := by
    refine ⟨2, 0, 1, ?_⟩
    norm_num [secondAgents, middle, destination]

theorem composite_not_separated :
    ¬ AgentsSeparated destination (second.agentMap ∘ first.agentMap) := by
  rintro ⟨a, b, e, h⟩
  fin_cases a <;> fin_cases b <;> fin_cases e <;>
    norm_num [second, first, firstAgents, secondAgents, source, destination,
      Function.comp_def] at h

theorem composite_environment_constant :
    ¬ EnvironmentVaries destination (second.agentMap ∘ first.agentMap) := by
  rintro ⟨a, e, d, h⟩
  fin_cases a <;> fin_cases e <;> fin_cases d <;>
    norm_num [second, first, firstAgents, secondAgents, source, destination,
      Function.comp_def] at h

end FiniteExample

theorem natural_composition_fails : Targets.NaturalCompositionFails := by
  exact ⟨FiniteExample.source, FiniteExample.middle, FiniteExample.destination,
    FiniteExample.first, FiniteExample.second,
    FiniteExample.composite_not_separated,
    FiniteExample.composite_environment_constant⟩

end LogicLineages.RL
