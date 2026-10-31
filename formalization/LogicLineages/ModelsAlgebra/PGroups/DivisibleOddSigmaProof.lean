module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleOddSigmaTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCompetitorProof
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

theorem divisible_product_odd_no_sigma : Targets.divisibleProductOddNoSigma := by
  classical
  intro R D _ _ _ _ p _ hR hD hr hd γ _ hl φ hc hs
  generalize hlevel : 2*γ+1=α at hc
  cases hc with
  | qf side q => exact ((by positivity : (2*γ+1:Ordinal)≠0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    obtain ⟨j,d,hmat⟩ := hs.1
    obtain ⟨H,inst,hct,_,hne,b,hbf⟩ := divisible_product_competitor R D p hR hD hr hd γ hl
      (0+m j) (append Fin.elim0 d)
    letI := inst
    letI : Countable H := hct
    have hβ : β j≤2*γ := Order.le_of_lt_succ (by simpa only [Order.succ_eq_add_one] using lower j)
    have hb := back_forth_monotone (2*γ) (β j) hβ (R×D) H (0+m j) _ _ hbf
    have ht := (truth_transfer (β j) (R×D) H (0+m j) _ _ hb).1 (matrix j) (rank j) hmat
    let c : Fin (m j) → H := fun i=>b (Fin.natAdd 0 i)
    have he : append (Fin.elim0 : Fin 0 → H) c = b := by
      funext i
      induction i using Fin.addCases with
      | left i => exact i.elim0
      | right i =>
        change Fin.addCases Fin.elim0 c (Fin.natAdd 0 i) = b (Fin.natAdd 0 i)
        rw [Fin.addCases_right]
    exact hne (hs.2 H ⟨j,c,by rw [he]; exact ht⟩)

theorem divisible_product_odd_no_raw_sigma : Targets.divisibleProductOddNoRawSigma := by
  intro R D _ _ _ _ p _ hR hD hr hd γ hγ hl φ hc hs
  exact divisible_product_odd_no_sigma R D p hR hD hr hd γ hγ hl φ hc
    (raw_scott_restriction (R×D) φ hs)
end LogicLineages.ModelsAlgebra.PGroups
