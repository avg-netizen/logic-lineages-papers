module

public import Mathlib.Data.Real.Basic

/-! The printed same-environment ranking contract, independently of any
proposed proof or policy conversion. -/
@[expose] public section

namespace LogicLineages.RL

structure Framework where
  Agent : Type
  Environment : Type
  value : Agent → Environment → ℝ

def Faithful (F G : Framework) (f : F.Agent → G.Agent)
    (g : G.Environment → F.Environment) : Prop :=
  ∀ a b e, G.value (f a) e < G.value (f b) e ↔
    F.value a (g e) < F.value b (g e)

def AgentsSeparated {A : Type} (G : Framework) (f : A → G.Agent) : Prop :=
  ∃ a b e, G.value (f a) e < G.value (f b) e

def EnvironmentVaries {A : Type} (G : Framework) (f : A → G.Agent) : Prop :=
  ∃ a e d, G.value (f a) e < G.value (f a) d

structure Transformation (F G : Framework) where
  agentMap : F.Agent → G.Agent
  environmentMap : G.Environment → F.Environment
  faithful : Faithful F G agentMap environmentMap
  agentsSeparated : AgentsSeparated G agentMap
  environmentVaries : EnvironmentVaries G agentMap

end LogicLineages.RL
