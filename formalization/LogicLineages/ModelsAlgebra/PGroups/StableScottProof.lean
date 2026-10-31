module
public import LogicLineages.ModelsAlgebra.PGroups.StableScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.StabilizationSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.StableTailCategoricityProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedScott
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem stable_group_table_exact : Targets.stableGroupTableExact := by
  intro p _ N entries socleEntry
  constructor
  · apply positive_pi_all_complexity 3 (by simp)
    intro φ hφ
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at hφ
    rcases hφ with (rfl | rfl | rfl) | ⟨i,rfl⟩
    · exact positive_complexity_monotone .pi 2 3 0 _ two_ne_zero
        (by exact_mod_cast (show (2:ℕ)≤3 from by decide)) (primary_sentence_exact.{0} p).1
    · exact positive_complexity_monotone .pi 2 3 0 _ two_ne_zero
        (by exact_mod_cast (show (2:ℕ)≤3 from by decide)) (stabilization_sentence_exact p N).1
    · exact positive_complexity_monotone .pi 2 3 0 _ two_ne_zero
        (by exact_mod_cast (show (2:ℕ)≤3 from by decide)) (socle_rank_entry_exact p N 0 socleEntry).1
    · exact (ulm_rank_entry.{0,0} p i.val 0 (entries i)).1
  · intro G _ _
    unfold stableGroupTable
    rw [pi_two_all_realization G 0]
    simp only [List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,and_true,
      List.forall_mem_ofFn_iff,(primary_sentence_exact.{0} p).2 G,
      (stabilization_sentence_exact p N).2 G,(socle_rank_entry_exact p N 0 socleEntry).2 G,
      (ulm_rank_entry.{0,0} p _ 0 _).2 G]
    tauto

theorem stable_pi_three_scott : Targets.stablePiThreeScott := by
  classical
  intro p _ G _ _ N hprimary hs
  obtain ⟨entries,he⟩ := countable_ulm_table_exists p G N
  let r := Module.rank (ZMod p) (pSocle p (finiteFiltration p N:AddSubgroup G))
  have hex : ∃ entry:Option ℕ, r=(match entry with | none=>Cardinal.aleph0 | some m=>(m:Cardinal)) := by
    by_cases h:r=Cardinal.aleph0
    · exact ⟨none,h⟩
    · exact ⟨some r.toNat,(Cardinal.cast_toNat_of_lt_aleph0
        (lt_of_le_of_ne (countable_socle_rank_bound p G _) h)).symm⟩
  obtain ⟨entry,hentry⟩ := hex
  refine ⟨stableGroupTable p N entries entry,(stable_group_table_exact p N entries entry).1,?_,?_⟩
  · exact ((stable_group_table_exact p N entries entry).2 G).mpr ⟨hprimary,hs,hentry,he⟩
  · intro H _ _ hH
    obtain ⟨hprimaryH,hsH,hrH,heH⟩ := ((stable_group_table_exact p N entries entry).2 H).mp hH
    apply stable_tail_categoricity G H p hprimary hprimaryH (N:Ordinal) hs hsH
    · intro β hβ
      obtain ⟨j,rfl⟩ := Ordinal.lt_omega0.mp (hβ.trans (Ordinal.natCast_lt_omega0 N))
      have hj:j<N := by exact_mod_cast hβ
      rw [finite_ordinal_filtration G p j,finite_ordinal_filtration H p j]
      exact (he ⟨j,hj⟩).trans (heH ⟨j,hj⟩).symm
    · rw [finite_ordinal_filtration G p N,finite_ordinal_filtration H p N]
      exact hentry.trans hrH.symm

theorem stable_raw_pi_three_scott : Targets.stableRawPiThreeScott := by
  intro p _ G _ _ N hp hs
  obtain ⟨φ,hφ,hscott⟩ := stable_pi_three_scott p G N hp hs
  exact ⟨guardPi φ,raw_guard_pi_complexity 3 (by norm_num) φ hφ,raw_guard_scott_transfer G φ hscott⟩
end LogicLineages.ModelsAlgebra.PGroups
