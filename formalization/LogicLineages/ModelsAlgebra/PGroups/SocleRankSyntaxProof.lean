module
public import LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunction
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranches
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

private theorem append_empty {G:Type} {n:ℕ} (a:Fin n→G) (d:Fin 0→G) : append a d=a := by
  funext i
  change Fin.addCases a d (Fin.castAdd 0 i)=a i
  exact Fin.addCases_left _

theorem socle_upper_dimension : Targets.socleUpperDimension := by
  intro p _ j n m
  constructor
  · exact dual_complexity .sigma 1 n _ (socle_lower_dimension p j n (m+1)).1
  · intro G _ a
    unfold socleUpperFormula
    rw [dual_realization,(socle_lower_dimension p j n (m+1)).2 G a]
    rw [not_le,Nat.cast_add,Nat.cast_one]
    exact Cardinal.lt_natCast_add_one_iff

theorem socle_infinite_dimension : Targets.socleInfiniteDimension := by
  intro p _ j n
  constructor
  · exact countable_conj_all_complexity 2 two_ne_zero ℕ n (fun _=>0)
      (fun m=>socleLowerFormula p j n m) (fun _=>1)
      (fun _=>one_lt_two) (fun m=>(socle_lower_dimension p j n m).1)
  · intro G _ a
    unfold infiniteSocleFormula
    rw [countable_conj_all_realization,Cardinal.aleph0_le]
    constructor
    · intro h m
      apply ((socle_lower_dimension p j n m).2 G a).mp
      simpa only [append_empty] using h m Fin.elim0
    · intro h m d
      have hm := ((socle_lower_dimension p j n m).2 G a).mpr (h m)
      simpa only [append_empty] using hm

theorem countable_socle_rank_bound : Targets.countableSocleRankBound := by
  intro p G _ _ S
  exact (rank_le_card (ZMod p) (pSocle p S)).trans Cardinal.mk_le_aleph0

theorem socle_rank_entry_exact : Targets.socleRankEntryExact := by
  intro p _ j n entry
  cases entry with
  | none =>
    refine ⟨(socle_infinite_dimension p j n).1,?_⟩
    intro G _ _ a
    rw [socleRankEntry,(socle_infinite_dimension p j n).2 G a]
    exact ⟨fun h=>le_antisymm (countable_socle_rank_bound p G _) h,fun h=>h.ge⟩
  | some m =>
    constructor
    · change Complexity .pi 2 (piConjunction (piWrap (socleLowerFormula p j n m)) (socleUpperFormula p j n m))
      apply pi_conjunction_complexity 2 two_ne_zero
      · exact pi_wrap_complexity 2 1 two_ne_zero one_lt_two n _ (socle_lower_dimension p j n m).1
      · exact positive_complexity_monotone .pi 1 2 n _ one_ne_zero one_le_two
          (socle_upper_dimension p j n m).1
    · intro G _ _ a
      change (piConjunction (piWrap (socleLowerFormula p j n m)) (socleUpperFormula p j n m)).Realize a ↔ _
      rw [pi_conjunction_realization,pi_wrap_realization,(socle_lower_dimension p j n m).2 G a,
        (socle_upper_dimension p j n m).2 G a]
      exact ⟨fun h=>le_antisymm h.2 h.1,fun h=>⟨h.ge,h.le⟩⟩
end LogicLineages.ModelsAlgebra.PGroups
