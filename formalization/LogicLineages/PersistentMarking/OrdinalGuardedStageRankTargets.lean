module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalGuardedStageRankTargets

def GuardedStageLaw {α : Type} (r : α → α → Prop) (domain : α → Prop)
    (stage : Ordinal.{0} → α → Prop) : Prop :=
  ∀ a q, stage a q ↔ domain q ∧ ∀ t, r t q → ∃ b < a, stage b t

def GuardedStageRankExact : Prop :=
  ∀ {α : Type} (r : α → α → Prop) (domain : α → Prop) (stage : Ordinal.{0} → α → Prop),
    GuardedStageLaw r domain stage →
    (∀ {s t}, domain s → r t s → domain t) →
    (∀ a q, stage a q ↔ domain q ∧ ∃ h : Acc r q, h.rank ≤ a) ∧
    (∀ q (h : Acc r q), domain q → IsLeast {a : Ordinal.{0} | stage a q} h.rank) ∧
    (∀ q, domain q → (∀ t, ¬ r t q) → stage 0 q)

end LogicLineages.PersistentMarking.OrdinalGuardedStageRankTargets
