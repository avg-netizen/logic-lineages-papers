import LogicLineages.PersistentMarking.MarkedConstructorIterationProof

namespace LogicLineages.PersistentMarking.MarkedConstructorStabilizationProof
open Spine FiniteDomainSchema HereditaryDomainCode
open MarkedConstructorOperator
open MarkedConstructorOperatorTargets (Endomap Monotone Stabilizes)
open MarkedConstructorIterationProof (retained ordered constantAfter fixedBelow)

theorem distinctLength (xs ys : List Code) (hd : xs.Pairwise (· ≠ ·)) (hs : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hn,hxs⟩ := List.pairwise_cons.mp hd
    have hy : x ∈ ys := hs List.mem_cons_self
    have hs' : xs ⊆ ys.erase x := by
      intro z hz
      exact (List.mem_erase_of_ne (Ne.symm (hn z hz))).mpr (hs (List.mem_cons_of_mem _ hz))
    have hb := ih (ys.erase x) hxs hs'
    rw [List.length_erase_of_mem hy] at hb
    have hpos := List.length_pos_of_mem hy
    simp only [List.length_cons]
    omega

theorem repeatFixed (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads)
    (i j : Nat) (hij : i < j) (h : iterate S E heads i = iterate S E heads j) :
    step S E heads (iterate S E heads i) = iterate S E heads i := by
  have hforward := ordered S E heads he hm i (i+1) (by omega)
  have hreverse := ordered S E heads he hm (i+1) j hij
  rw [← h] at hreverse
  exact (MarkedFamilyOrderProof.partialOrder E heads).2.2 _ _
    (retained S E heads he (i+1)) (retained S E heads he i) hreverse hforward

theorem fixedAtBound (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads) :
    step S E heads (leastFixedPoint S E heads) = leastFixedPoint S E heads := by
  let members := MarkedFamilyCoherence.retained E heads
  let n := members.length
  change step S E heads (iterate S E heads n) = iterate S E heads n
  by_cases hfix : step S E heads (iterate S E heads n) = iterate S E heads n
  · exact hfix
  · exfalso
    have hdistinct : ((List.range (n+1)).map (iterate S E heads)).Pairwise (· ≠ ·) := by
      apply List.pairwise_map.mpr
      refine List.pairwise_lt_range.imp_of_mem ?_
      intro i j hi hj hij hr
      have hjn : j ≤ n := by have h := List.mem_range.mp hj; omega
      have hin : i ≤ n := by omega
      have hi' := repeatFixed S E heads he hm i j hij hr
      have hni := constantAfter S E heads i hi' n hin
      exact hfix (by rw [hni]; exact hi')
    have hsub : (List.range (n+1)).map (iterate S E heads) ⊆ members := by
      intro c hc
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
      exact retained S E heads he i
    have hlen := distinctLength _ members hdistinct hsub
    simp only [List.length_map,List.length_range] at hlen
    change n+1 ≤ n at hlen
    omega

theorem stabilizes (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads) : Stabilizes S E heads := by
  have hfix := fixedAtBound S E heads he hm
  refine ⟨retained S E heads he,ordered S E heads he hm,?_,hfix,?_⟩
  · intro n hn
    exact constantAfter S E heads _ hfix n hn
  · intro M hM hMfix
    exact fixedBelow S E heads he hm M hM hMfix _

end LogicLineages.PersistentMarking.MarkedConstructorStabilizationProof
