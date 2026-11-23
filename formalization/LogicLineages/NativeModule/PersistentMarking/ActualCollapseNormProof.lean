module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseTargets
public import LogicLineages.PersistentMarking.ActualOmegaTowerProof
public import LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaProof

@[expose] public section

/-! Norm layer: `|a_n| ≤ 1`, norms are countable, and below `Λ` the ordinals of norm below a
countable `θ` form a countable set (the hereditary base-Ω representation with coefficients and
exponent norms below `θ`). -/

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal ActualOmegaTower
open scoped Ordinal

theorem one_lt_index : (1 : Ordinal.{0}) < omegaIndex := one_lt_omega0.trans omega0_lt_omega_one

theorem zero_lt_omegaOne : (0 : Ordinal.{0}) < ω₁ := zero_lt_one.trans one_lt_index

theorem norm_eq (o : Ordinal.{0}) : coefficientNorm o =
    ((CNF omegaIndex o).map (fun p => max p.2 (if h : p.1 < o then coefficientNorm p.1 else 0))).foldr max 0 := by
  rw [coefficientNorm]

theorem le_foldr_max {L : List Ordinal.{0}} {x : Ordinal.{0}} (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => cases h
  | cons y L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_lt {L : List Ordinal.{0}} {b : Ordinal.{0}} (h0 : 0 < b) (h : ∀ x ∈ L, x < b) :
    L.foldr max 0 < b := by
  induction L with
  | nil => exact h0
  | cons y L ih =>
    exact max_lt (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem normBelowOmegaOne : NormBelowOmegaOne := by
  intro o
  refine Ordinal.induction (p := fun o => coefficientNorm o < ω₁) o (fun o ih => ?_)
  rw [norm_eq]
  refine foldr_max_lt zero_lt_omegaOne (fun x hx => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine max_lt (CNF.snd_lt one_lt_index hp) ?_
  split
  · next h => exact ih _ h
  · exact zero_lt_omegaOne

theorem argument_zero : argument 0 = 0 := exact_LiteralRecurrence.2.1

theorem argument_succ (n : Nat) : argument (n + 1) = omegaIndex ^ argument n :=
  exact_LiteralRecurrence.2.2.2.2 n

theorem cnf_power (e : Ordinal.{0}) : CNF omegaIndex (omegaIndex ^ e) = [(e, 1)] := by
  have h := CNF.opow_mul_add (b := omegaIndex) (e := e) (x := 1) (y := 0) one_lt_index one_ne_zero
    one_lt_index (opow_pos _ (zero_lt_one.trans one_lt_index))
  simpa using h

theorem normBound : NormBound := by
  intro n
  induction n with
  | zero =>
    rw [argument_zero, norm_eq, CNF.zero_right]
    exact zero_le_one
  | succ n ih =>
    rw [argument_succ, norm_eq, cnf_power]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    refine max_le (max_le le_rfl ?_) zero_le_one
    split
    · exact ih
    · exact zero_le_one

theorem log_lt_self_below {η : Ordinal.{0}} (hη : η < endpoint) (h0 : η ≠ 0) :
    log omegaIndex η < η := by
  rcases (log_le_self omegaIndex η).lt_or_eq with h | h
  · exact h
  · exfalso
    have hle : omegaIndex ^ η ≤ η := by
      have := opow_log_le_self omegaIndex h0
      rwa [h] at this
    exact absurd (exact_EndpointLeast η hle) (not_le.2 hη)

/-- Each Cantor-normal-form entry of `η < Λ` has its exponent below `η`, and its coefficient and
exponent norm bounded by `|η|`. -/
theorem entry_le {η : Ordinal.{0}} {p : Ordinal.{0} × Ordinal.{0}} (hη : η < endpoint)
    (hp : p ∈ CNF omegaIndex η) :
    p.1 < η ∧ p.2 ≤ coefficientNorm η ∧ coefficientNorm p.1 ≤ coefficientNorm η := by
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at hp
  have hlt : p.1 < η := (CNF.fst_le_log hp).trans_lt (log_lt_self_below hη h0)
  have mem : max p.2 (if h : p.1 < η then coefficientNorm p.1 else 0) ≤ coefficientNorm η := by
    rw [norm_eq η]
    exact le_foldr_max (List.mem_map.2 ⟨p, hp, rfl⟩)
  rw [dif_pos hlt] at mem
  exact ⟨hlt, (le_max_left _ _).trans mem, (le_max_right _ _).trans mem⟩

theorem levelCountable (θ : Ordinal.{0}) (hθ : θ < ω₁) :
    ∀ n, Set.Countable {η : Ordinal.{0} | η < argument n ∧ coefficientNorm η < θ} := by
  have hIio : (Set.Iio θ).Countable := by
    have h := (OrdinalCountablePrefixOmegaProof.exact_CountablePrefixIffBelowOmegaOne θ).2 hθ
    exact Set.countable_coe_iff.1 h
  intro n
  induction n with
  | zero =>
    refine Set.Countable.mono (fun η h => ?_) Set.countable_empty
    have h1 := h.1
    rw [argument_zero] at h1
    exact (not_lt_zero h1).elim
  | succ n ih =>
    let T : Set (Ordinal.{0} × Ordinal.{0}) :=
      {η | η < argument n ∧ coefficientNorm η < θ} ×ˢ Set.Iio θ
    have hT : T.Countable := ih.prod hIio
    haveI : Countable T := hT.to_subtype
    let ev : List T → Ordinal.{0} := fun l =>
      (l.map Subtype.val).foldr (fun p r => omegaIndex ^ p.1 * p.2 + r) 0
    refine (Set.countable_range ev).mono ?_
    rintro η ⟨hη, hn⟩
    have hηΛ : η < endpoint := hη.trans (exact_BelowEndpoint (n+1))
    have mem : ∀ p ∈ CNF omegaIndex η, p ∈ T := by
      intro p hp
      have h0 : η ≠ 0 := by
        rintro rfl
        simp at hp
      obtain ⟨_, hc, he⟩ := entry_le hηΛ hp
      have hpow : η < omegaIndex ^ argument n := by
        rw [← argument_succ]
        exact hη
      refine ⟨⟨?_, he.trans_lt hn⟩, hc.trans_lt hn⟩
      exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt one_lt_index h0).1 hpow)
    refine ⟨(CNF omegaIndex η).attach.map (fun p => (⟨p.1, mem p.1 p.2⟩ : T)), ?_⟩
    have hl : ((CNF omegaIndex η).attach.map (fun p => (⟨p.1, mem p.1 p.2⟩ : T))).map Subtype.val =
        CNF omegaIndex η := by
      simp only [List.map_map, Function.comp_def]
      exact List.attach_map_subtype_val _
    show ((((CNF omegaIndex η).attach.map (fun p => (⟨p.1, mem p.1 p.2⟩ : T))).map Subtype.val).foldr
      (fun p r => omegaIndex ^ p.1 * p.2 + r) 0) = η
    rw [hl]
    exact CNF.foldr _ _

theorem normCountable : NormCountable := by
  intro θ hθ
  refine (Set.countable_iUnion (levelCountable θ hθ)).mono ?_
  rintro η ⟨h, hn⟩
  obtain ⟨n, hn'⟩ := (exact_Cofinal η).1 h
  exact Set.mem_iUnion.2 ⟨n, hn', hn⟩

end LogicLineages.PersistentMarking.ActualCollapse
