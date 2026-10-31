module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedOddSigmaTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferComparisonProof
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem reduced_odd_no_sigma : Targets.reducedOddNoSigma := by
  classical
  intro G _ _ p _ hG hr γ _ hl φ hc hs
  let Q := G×PrueferModel p
  let i : G → Q := fun x=>(x,0)
  letI : Countable Q := (pruefer_enlargement_data G p hG).1
  have hne := reduced_pruefer_enlargement_noniso G p hr
  generalize hlevel : 2*γ+1=α at hc
  cases hc with
  | qf side q => exact ((by positivity : (2*γ+1:Ordinal)≠0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    obtain ⟨j,d,hd⟩ := hs.1
    have hb := reduced_pruefer_comparison G p hG hr γ hl (0+m j) (append Fin.elim0 d)
    have hβ : β j≤2*γ := Order.le_of_lt_succ (by simpa only [Order.succ_eq_add_one] using lower j)
    have hbf := back_forth_monotone (2*γ) (β j) hβ G Q (0+m j) _ _ hb
    have ht := (truth_transfer (β j) G Q (0+m j) _ _ hbf).1 (matrix j) (rank j) hd
    have hnil : (fun k:Fin 0=>i (Fin.elim0 k))=Fin.elim0 := by funext k; exact Fin.elim0 k
    change (matrix j).Realize (fun k=>i (append Fin.elim0 d k)) at ht
    rw [hom_append,hnil] at ht
    exact hne (hs.2 Q ⟨j,fun k=>i (d k),ht⟩)

theorem reduced_odd_no_raw_sigma : Targets.reducedOddNoRawSigma := by
  intro G _ _ p _ hG hr γ hγ hl φ hc hs
  exact reduced_odd_no_sigma G p hG hr γ hγ hl φ hc (raw_scott_restriction G φ hs)
end LogicLineages.ModelsAlgebra.PGroups
