module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationJobs

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
open LiteralDerivationTree LiteralDerivationLocalityTargets
open NumberedWindowSimulationJobs NumberedWindowDomain
open DecisionInventory (auxiliarySupport)

theorem localBound {S K J} {d : Tree S J} (h : Foot K d) :
    ∀ ρ, ρ ∈ localTypes d → ρ ∈ K := by
  intro ρ hρ
  apply h
  rw [footprint.eq_def]
  exact List.mem_append_left _ hρ

theorem rootBound {S K J} {d : Tree S J} (h : Foot K d) :
    ∀ ρ, ρ ∈ rootTypes J → ρ ∈ K := by
  intro ρ hρ
  apply localBound h
  exact List.mem_append_left _ hρ

theorem weakSource {S K q t} {d : Tree S (.weak q t)} (h : Foot K d) :
    SymbolicAdmissible K q := by
  intro ρ hρ
  exact rootBound h ρ (List.mem_append_left _ hρ)

theorem weakTarget {S K q t} {d : Tree S (.weak q t)} (h : Foot K d) :
    SymbolicAdmissible K t := by
  intro ρ hρ
  exact rootBound h ρ (List.mem_append_right _ hρ)

theorem strictSource {S K q t} {d : Tree S (.strict q t)} (h : Foot K d) :
    SymbolicAdmissible K q := by
  intro ρ hρ
  exact rootBound h ρ (List.mem_append_left _ hρ)

end LogicLineages.PersistentMarking.NumberedWindowSimulationFootProof
