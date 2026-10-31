module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem collect_codes {α : Type} (n : Nat) (f : Fin n → Option α) (enc : α → List Nat) :
    collectLists (List.ofFn (fun i => (f i).map enc)) =
      (AdmissibleAssignment.collect n f).map (fun v => List.ofFn (fun i => enc (v i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, collectLists, AdmissibleAssignment.collect]
    rw [ih]
    cases hf : f 0 <;> cases hr : AdmissibleAssignment.collect n (fun i => f i.succ) <;>
      simp [List.ofFn_succ]

private theorem range_map {α : Type} (n : Nat) (f : Nat → α) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk; simp

private theorem lookup {n : Nat} (f : Fin n → Nat) (j : Fin n) :
    (List.ofFn f).getD j.val 0 = f j := by
  simp [List.getD_eq_getElem?_getD, j.isLt]

theorem ordinalSyntaxPartialsCodeCorrect : Targets.OrdinalSyntaxPartialsCodeCorrect := by
  intro Γ σ m h
  unfold partialsCode
  rw [range_map]
  have hi : (fun i : Fin (m+1) => partialRun σ.level i.val ((vectorCode h).getD i.val 0)) =
      (fun i => (AdmissiblePartial.run allLeftPolicy i.val (h i)).map
        (fun v => List.ofFn (fun j => typedCode (v j)))) := by
    funext i
    rw [show (vectorCode h).getD i.val 0 = typedCode (h i) from lookup _ i]
    exact ordinalSyntaxPartialCorrect Γ σ i.val (h i)
  rw [hi]
  exact collect_codes _ _ _
theorem ordinalSyntaxAbstractionCorrect : Targets.OrdinalSyntaxAbstractionCorrect := by
  intro Γ σ m h
  rw [abstractionCode, ordinalSyntaxPartialsCodeCorrect Γ σ m h]
  unfold AdmissibleAssignment.abstraction
  cases hc : AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run allLeftPolicy i.val (h i)) with
  | none => simp
  | some ps =>
    simp only [Option.map_some, Option.bind_some, Bind.bind, Pure.pure]
    apply congrArg some
    have hsizes : ((vectorCode h).map partialSize).sum =
        ((List.ofFn h).map ordinalPartialSize).sum := by
      congr 1
      simp only [vectorCode, List.map_ofFn]
      congr 1
      funext i
      exact ordinalSyntaxPartialSizeCorrect Γ σ (h i)
    let factor := 2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum
    have hscalar : ((List.ofFn (fun i => List.ofFn (fun j => typedCode (ps i j)))).getD 0 []).getD 0 0 =
        typedCode (ps 0 0) := by simp [List.getD_eq_getElem?_getD]
    have hp (j : Nat) (hj : j < σ.level+2) :
        sumPrefix m ((List.ofFn (fun i => List.ofFn (fun k => typedCode (ps i k)))).map (fun row => row.getD j 0)) =
          typedCode (AdmissibleSum.expand (leftShape m) (fun i => ps i ⟨j,hj⟩)) := by
      have he : (fun i : Fin (m+1) => (List.ofFn (fun k => typedCode (ps i k))).getD j 0) =
          (fun i => typedCode (ps i ⟨j,hj⟩)) := by
        funext i
        exact lookup _ ⟨j,hj⟩
      rw [List.map_ofFn]
      dsimp only [Function.comp_def]
      rw [he]
      exact ordinalSyntaxSumCorrect Γ m _
    have hh (j : Nat) (hj : j < m+1) : headClosure ((vectorCode h).getD j 0) =
        typedCode (ordinalHeadClosure (h ⟨j,hj⟩)) := by
      rw [show (vectorCode h).getD j 0 = typedCode (h ⟨j,hj⟩) from lookup _ ⟨j,hj⟩]
      exact ordinalSyntaxHeadClosureCorrect Γ σ _
    dsimp only [vectorCode] at hh
    rw [abstractionResult, hsizes, range_map]
    unfold vectorCode
    congr 1
    funext j
    by_cases hzero : j.val=0
    · have hm : j.val<m+1 := by omega
      simp only [hzero, if_true, show (0:Nat)<m+1 by omega, dif_pos, hscalar]
      rw [ordinalSyntaxRepeatCorrect Γ .scalarRepeat _ (ps 0 0), hh 0 (by omega)]
      rfl
    · simp only [if_neg hzero]
      by_cases hl : j.val<σ.level+2
      · simp only [if_pos hl, dif_pos hl]
        rw [hp j.val hl]
        by_cases hm : j.val<m+1
        · simp only [if_pos hm, dif_pos hm]
          rw [hh j.val hm]
          rfl
        · simp only [if_neg hm, dif_neg hm]
          rfl
      · have hm : j.val<m+1 := by have := j.isLt; omega
        simp only [if_neg hl, dif_neg hl, if_pos hm, dif_pos hm]
        rw [hh j.val hm]
        rfl
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
