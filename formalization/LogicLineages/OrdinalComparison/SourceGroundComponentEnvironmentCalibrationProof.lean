module
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentTargets
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsCoordinatesProof
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof
public import Mathlib.Data.List.GetD

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Proof

private theorem member_le_foldr_max {a : Nat} {xs : List Nat} (h : a ∈ xs) :
    a ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldr_cons]
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem pair_lt_bound {n j : Nat} (hj : j < n) : Nat.pair j 0 < bound n := by
  have hm : Nat.pair j 0 ∈ (List.range n).map (fun k => Nat.pair k 0) :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have hh := member_le_foldr_max hm
  unfold bound
  omega

private theorem lookup_in_bounds (xs : List Nat) (k : Nat) (hk : k < bound xs.length) :
    (environment xs).getD k 0 = slot xs k := by
  have hlen : k < (environment xs).length := by simpa [environment] using hk
  rw [List.getD_eq_getElem (environment xs) 0 hlen]
  simp [environment]

theorem exactLayout : Targets.ExactLayout := by
  intro xs
  refine ⟨by simp [environment], ?_, ?_⟩
  · intro j hj
    rw [lookup_in_bounds xs (Nat.pair j 0) (pair_lt_bound hj)]
    simp [slot, Nat.unpair_pair]
  · intro k hk
    by_cases hb : k < bound xs.length
    · rw [lookup_in_bounds xs k hb]
      simp only [slot, if_neg hk]
    · apply List.getD_eq_default
      simpa only [environment, List.length_map, List.length_range] using Nat.le_of_not_gt hb

theorem typedLookup : Targets.TypedLookup := by
  intro Γ xs hΓ hlen c
  rcases c with ⟨σ, x, j⟩
  have hs := SourceMachineRawValuations.Proof.variable_ground hΓ x
  cases hs
  have hj : j = 0 := Fin.eq_zero j
  subst j
  change (environment xs).getD (Nat.pair (SourceTypedPorts.variableIndex x) 0) 0 =
    xs.getD (SourceTypedPorts.variableIndex x) 0
  apply (exactLayout xs).2.1
  rw [hlen]
  exact SourceTypedPortsProof.typedVariableIndex.1 Γ .ground x

end LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Proof
