module
public import LogicLineages.PermittedControl.MixedRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankResidue
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)

private theorem rankPresentExact (rank : Nat) (ranks : List Nat) :
    rankPresent rank ranks = true ↔ rank ∈ ranks := by
  induction ranks with
  | nil => simp [rankPresent]
  | cons r rs ih =>
    change (if r = rank then true else rankPresent rank rs) = true ↔ rank ∈ r :: rs
    by_cases same : r = rank
    · simp [same]
    · rw [if_neg same,ih]
      simp [Ne.symm same]

private theorem memRecordRank (r key : Nat) (ranks : List Nat) :
    r ∈ recordRank key ranks ↔ r = key ∨ r ∈ ranks := by
  unfold recordRank
  by_cases present : rankPresent key ranks = true
  · rw [if_pos present]
    have keyMember := (rankPresentExact key ranks).mp present
    exact ⟨Or.inr,fun h => h.elim (fun e => by simpa only [e] using keyMember) id⟩
  · simp [present]

private theorem nodupRecordRank (key : Nat) (ranks : List Nat) (unique : ranks.Nodup) :
    (recordRank key ranks).Nodup := by
  unfold recordRank
  by_cases present : rankPresent key ranks = true
  · simpa only [if_pos present] using unique
  · rw [if_neg present]
    exact List.nodup_cons.mpr ⟨fun h => present ((rankPresentExact key ranks).mpr h),unique⟩

private theorem rankSupportMembers (terms : List WeightedOperand) : (rankSupport terms).Nodup ∧
    ∀ rank, rank ∈ rankSupport terms ↔ ∃ t ∈ terms, t.2.rank = rank := by
  induction terms with
  | nil => simp [rankSupport]
  | cons t ts ih =>
    change (recordRank t.2.rank (rankSupport ts)).Nodup ∧
      ∀ rank, rank ∈ recordRank t.2.rank (rankSupport ts) ↔ ∃ u ∈ t :: ts, u.2.rank = rank
    refine ⟨nodupRecordRank t.2.rank _ ih.1,?_⟩
    intro rank
    rw [memRecordRank,ih.2]
    constructor
    · rintro (same | ⟨u,mem,eq⟩)
      · exact ⟨t,List.mem_cons_self,same.symm⟩
      · exact ⟨u,List.mem_cons_of_mem _ mem,eq⟩
    · rintro ⟨u,mem,eq⟩
      rcases List.mem_cons.mp mem with same | later
      · subst u
        exact Or.inl eq.symm
      · exact Or.inr ⟨u,later,eq⟩

private theorem lookupMap (val : Nat → Nat) (rank : Nat) (keys : List Nat) (used : rank ∈ keys) :
    lookup rank (keys.map (fun key => (key,val key))) = val rank := by
  induction keys with
  | nil => simp at used
  | cons key keys ih =>
    change (if key = rank then val key else lookup rank (keys.map (fun k => (k,val k)))) = val rank
    by_cases same : key = rank
    · simp [same]
    · rw [if_neg same]
      exact ih ((List.mem_cons.mp used).resolve_left (Ne.symm same))

theorem rankSupportExact : RankSupport := by
  exact ⟨rankSupportMembers,fun m terms ρ rank used =>
    lookupMap (fun r => ρ r % (2*m)) rank (rankSupport terms) used⟩

end LogicLineages.PermittedControl.MixedRankResidue
