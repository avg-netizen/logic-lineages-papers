module
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawConjunction
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunction
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth
private theorem append_empty {G:Type} {n:ℕ} (a:Fin n→G) (d:Fin 0→G) : append a d=a := by
  funext i
  simpa [append] using (Fin.addCases_left (m:=n) (n:=0) (motive:=fun _=>G) (left:=a) (right:=d) i)

theorem positive_complexity_monotone : Targets.positiveComplexityMonotone := by
  intro side α β hα hab n φ hc
  cases hc with
  | qf side q => exact (hα rfl).elim
  | sigma hpos s m matrix ranks lower rank =>
    exact Complexity.sigma (ne_of_gt ((bot_lt_iff_ne_bot.mpr hpos).trans_le hab))
      s m matrix ranks (fun i=>(lower i).trans_le hab) rank
  | pi hpos s m matrix ranks lower rank =>
    exact Complexity.pi (ne_of_gt ((bot_lt_iff_ne_bot.mpr hpos).trans_le hab))
      s m matrix ranks (fun i=>(lower i).trans_le hab) rank

theorem raw_pi_normalization : Targets.rawPiNormalization := by
  intro α β hβ hab n φ hc
  cases hc with
  | qf side q =>
    refine ⟨(pi_qf_padding.{0,0} β hβ n q).1,?_⟩
    intro G R a
    change (∀i:({0}:Set ℕ),∀d:Fin 0→G,q.RawRealize R (append a d)) ↔ q.RawRealize R a
    constructor
    · intro h
      simpa only [append_empty] using h ⟨0,by simp⟩ Fin.elim0
    · intro h i d
      simpa only [append_empty] using h
  | pi hpos s m matrix ranks lower rank =>
    refine ⟨?_,fun _ _ _=>Iff.rfl⟩
    exact positive_complexity_monotone .pi _ β hpos hab n _ (Complexity.pi hpos s m matrix ranks lower rank)

private theorem raw_disjunction (ι:Type) [Countable ι] (n:ℕ) (m:ι→ℕ)
    (matrix:(i:ι)→Formula (n+m i)) (G:Type) (R:RawGroupStructure G) (a:Fin n→G) :
    (countableDisjEx m matrix).RawRealize R a ↔ ∃i:ι,∃d:Fin (m i)→G,(matrix i).RawRealize R (append a d) := by
  let e := branchEquiv ι
  change (∃k:branchIndices ι,∃d:Fin (m (e.symm k))→G,(matrix (e.symm k)).RawRealize R (append a d)) ↔ _
  constructor
  · rintro ⟨k,d,hd⟩
    exact ⟨e.symm k,d,hd⟩
  · rintro ⟨i,d,hd⟩
    refine ⟨e i,?_⟩
    rw [e.symm_apply_apply]
    exact ⟨d,hd⟩

theorem raw_wrapper_truth : Targets.rawWrapperTruth := by
  intro n φ G R a
  constructor
  · unfold piWrap
    rw [raw_countable_conjunction Unit n _ _ G R a]
    constructor
    · intro h
      simpa only [append_empty] using h () Fin.elim0
    · intro h i d
      simpa only [append_empty] using h
  · unfold sigmaWrap
    rw [raw_disjunction Unit n _ _ G R a]
    constructor
    · rintro ⟨i,d,hd⟩
      simpa only [append_empty] using hd
    · intro h
      exact ⟨(),Fin.elim0,by simpa only [append_empty] using h⟩

theorem raw_difference_pi_lift : Targets.rawDifferencePiLift := by
  intro α β hab n d hd
  have hb : β≠0 := ne_of_gt (lt_of_le_of_lt zero_le hab)
  have hp := raw_pi_normalization α β hb hab.le n d.piPart hd.2
  refine ⟨pi_conjunction_complexity β hb n _ _
    (pi_wrap_complexity β α hb hab n d.sigmaPart hd.1) hp.1,?_⟩
  intro G R a
  change (piConjunction (piWrap d.sigmaPart) (piOneNormalize d.piPart)).RawRealize R a ↔ _
  rw [raw_pi_conjunction, (raw_wrapper_truth n d.sigmaPart G R a).1,hp.2 G R a]
  rfl
end LogicLineages.ModelsAlgebra.PGroups
