module
public import LogicLineages.PermittedControl.SelectedBoxAmbientProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoxHeadProof
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment Source.AdmissiblePartial

private theorem expand_head (ctrl : Nat → Nat) {Γ : List Ty} {σ : Ty} {n i : Nat}
    (s : Shape n) (xs : Fin n → OrdinalExpression (σ :: Γ))
    (h : ∀ j, HeadGrade ctrl Γ σ i (xs j)) : HeadGrade ctrl Γ σ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j))) (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem three_head (ctrl : Nat → Nat) {Γ : List Ty} {σ : Ty} {i : Nat}
    (p : Policy) (site : MacroSite) {a b c : OrdinalExpression (σ :: Γ)}
    (ha : HeadGrade ctrl Γ σ i a) (hb : HeadGrade ctrl Γ σ i b) (hc : HeadGrade ctrl Γ σ i c) :
    HeadGrade ctrl Γ σ i (three p site a b c) := by
  apply expand_head ctrl
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

 theorem headTailGrade : SelectedBoxTargets.HeadTailGrade := by
  intro ctrl Γ σ p n f g hf hg
  by_cases hn : n = 0
  · subst n
    simp only [boxTail,if_pos rfl]
    exact .add hf hg
  · have hnum : HeadGrade ctrl Γ σ 0 (numeral p n) := by
      cases n with
      | zero => contradiction
      | succ n => exact expand_head ctrl _ _ (fun _ => .one 0)
    rw [boxTail,if_neg hn]
    exact three_head ctrl p .optionalBoxTail hf hg hnum

 theorem positiveHeadGrade (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (m n : Nat)
    (hnm : n < m) (f : OrdinalVector (σ :: Γ) m) (g : OrdinalVector (σ :: Γ) n)
    (hf : ∀ j, HeadGrade ctrl Γ σ j.val (f j)) (hg : ∀ j, HeadGrade ctrl Γ σ j.val (g j))
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    HeadGrade ctrl Γ σ i (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    apply HeadGrade.emul hi
    · exact positiveHeadGrade ctrl Γ σ m n hnm f g hf hg (i+1) (by omega) (by omega)
    · apply HeadGrade.add
      · simpa only [ordinalVectorAt,dif_pos (by omega : i < m+1)] using hf ⟨i,by omega⟩
      · simpa only [ordinalVectorAt,dif_pos (by omega : i < n+1)] using hg ⟨i,by omega⟩
  · simpa only [ordinalVectorAt,dif_pos (by omega : i < m+1)] using hf ⟨i,by omega⟩
termination_by n+1-i
decreasing_by omega

 theorem headBox : SelectedBoxTargets.HeadBox := by
  intro ctrl K hctrl Γ σ m n hnm p f g hf hg bf bg
  have af : ∀ j, AmbientGrade ctrl (σ :: Γ) j.val (f j) :=
    fun j => SelectedGradedPositivityProof.head_ambient ctrl (hf j)
  have ag : ∀ j, AmbientGrade ctrl (σ :: Γ) j.val (g j) :=
    fun j => SelectedGradedPositivityProof.head_ambient ctrl (hg j)
  have hguard := SelectedBoxAmbientProof.boxGuard ctrl K hctrl (σ :: Γ) m n hnm p f g af ag bf bg
  refine ⟨?_,(SelectedBoxAmbientProof.ambientBox ctrl K hctrl (σ :: Γ) m n hnm p f g af ag bf bg).2⟩
  intro j
  rw [box]
  split
  · rename_i hj
    rw [hj]
    exact .collapse (positiveHeadGrade ctrl Γ σ m n hnm f g hf hg 1 (by omega) (by omega))
      (headTailGrade ctrl Γ σ p n (f 0) (g 0) (hf 0) (hg 0)) hguard
  · rename_i hj
    exact positiveHeadGrade ctrl Γ σ m n hnm f g hf hg j.val (by omega) (by have := j.isLt; omega)

 theorem fullSelectedBox : SelectedBoxTargets.FullSelectedBox :=
  ⟨SelectedBoxTailProof.tailGradeAndNorm,headTailGrade,SelectedBoxAmbientProof.boxGuard,
    SelectedBoxAmbientProof.ambientBox,headBox⟩

end LogicLineages.PermittedControl.SelectedBoxHeadProof
