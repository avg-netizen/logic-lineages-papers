module
public import LogicLineages.ModelsAlgebra.PGroups.CloseAllTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenaming
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

private theorem empty_left_lift (G:Type) (n:ℕ) (w:Fin n→G) :
    (fun i=>append (Fin.elim0:Fin 0→G) w (Fin.natAdd 0 i))=w := by
  funext i
  exact Fin.addCases_right (m:=0) (n:=n) (motive:=fun _=>G)
    (left:=(Fin.elim0:Fin 0→G)) (right:=w) i

private theorem append_split (G:Type) (n m:ℕ) (w:Fin (n+m)→G) :
    append (fun i=>w (Fin.castAdd m i)) (fun i=>w (Fin.natAdd n i))=w := by
  funext i
  induction i using Fin.addCases <;> simp only [append,Fin.addCases_left,Fin.addCases_right]

theorem sigma_close_all_correct : Targets.sigmaCloseAllCorrect := by
  intro α hα n φ hc
  cases hc with
  | qf side q => exact (hα rfl).elim
  | sigma hpos s m matrix β lower rank =>
    refine ⟨Complexity.sigma hpos s (fun i=>n+m i)
      (fun i=>renameFormula (Fin.natAdd 0) (matrix i)) β lower
      (fun i=>infinitary_renaming_complexity .pi (β i) _ _ (Fin.natAdd 0) (matrix i) (rank i)),?_⟩
    intro G _
    change (∃i:s,∃w:Fin (n+m i)→G,
      (renameFormula (Fin.natAdd 0) (matrix i)).Realize (append Fin.elim0 w)) ↔
        ∃a:Fin n→G,∃i:s,∃d:Fin (m i)→G,(matrix i).Realize (append a d)
    simp only [infinitary_renaming_realization G,empty_left_lift G]
    constructor
    · rintro ⟨i,w,hw⟩
      refine ⟨(fun j=>w (Fin.castAdd (m i) j)),i,(fun j=>w (Fin.natAdd n j)),?_⟩
      rw [append_split]
      exact hw
    · rintro ⟨a,i,d,hd⟩
      exact ⟨i,append a d,hd⟩

theorem pi_close_all_correct : Targets.piCloseAllCorrect := by
  classical
  intro α hα n φ hc
  have hd := dual_complexity .pi α n φ hc
  obtain ⟨hs,hsem⟩ := sigma_close_all_correct α hα n φ.dual hd
  refine ⟨dual_complexity .sigma α 0 (sigmaCloseAll φ.dual) hs,?_⟩
  intro G _
  change (sigmaCloseAll φ.dual).dual.Realize (Fin.elim0:Fin 0→G) ↔ _
  rw [dual_realization G 0 (sigmaCloseAll φ.dual) Fin.elim0,hsem G]
  simp only [not_exists,dual_realization G n φ,not_not]

end LogicLineages.ModelsAlgebra.PGroups
