module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitTargets
public import LogicLineages.OrdinalComparison.SourceOneUnitSizeProof
public import LogicLineages.PermittedControl.SelectedHardnessUnusedProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ControlSensitivityCurrent
open AdmissibleAssignment AdmissibleSum
open OneUnit.Proof (free_add size_add_active size_add_ge_right size_pos sum_ofFn_strict_head multiplier_positive)
open LogicLineages.PermittedControl.SelectedHardnessUnusedProof (unusedVector unused_assignment)

/-- The real ordered tree selected by p. Each operand occurrence remains a
separate unnormalized copy, even when its denotation equals another's. -/
def shapeCopies {Γ : List Ty} {n : Nat} (s : Shape n) (e : OrdinalExpression Γ) :
    OrdinalExpression Γ := expand s (fun _ => e)

theorem shapeCopiesActiveSize {Γ : List Ty} {σ : Ty} {n : Nat} (s : Shape n)
    (e : OrdinalExpression (σ :: Γ)) (he : ordinalHeadFree e = false) :
    ordinalHeadFree (shapeCopies s e) = false ∧
      ordinalPartialSize (shapeCopies s e) = n*ordinalPartialSize e+(n-1) := by
  induction s with
  | leaf => exact ⟨he,by simp [shapeCopies,expand]⟩
  | @join n m a b ia ib =>
    obtain ⟨ha,sa⟩ := ia
    obtain ⟨hb,sb⟩ := ib
    have hn := PolicyGadget.smallShapes.1 n a
    have hm := PolicyGadget.smallShapes.1 m b
    have hact : ordinalHeadFree (.add (shapeCopies a e) (shapeCopies b e)) = false := by
      rw [free_add,ha,hb] <;> rfl
    refine ⟨hact,?_⟩
    change ordinalPartialSize (.add (shapeCopies a e) (shapeCopies b e)) = _
    rw [size_add_active _ _ hact,sa,sb,Nat.add_mul]
    omega

theorem repeatedActiveSize (p : Policy) (site : MacroSite) {Γ : List Ty} {σ : Ty}
    (k : Nat) (hk : 0 < k) (e : OrdinalExpression (σ :: Γ)) (he : ordinalHeadFree e = false) :
    ordinalHeadFree (repeated p site k e) = false ∧
      ordinalPartialSize (repeated p site k e) = k*ordinalPartialSize e+(k-1) := by
  cases k with
  | zero => omega
  | succ k => exact shapeCopiesActiveSize (p.shape site k) e he

theorem inflatedSize (p : Policy) {Γ : List Ty} {σ τ : Ty}
    (e : OrdinalExpression (σ :: Γ)) (he : ordinalHeadFree e = false) :
    ordinalPartialSize (inflated p τ e) = OneUnit.coefficient τ*ordinalPartialSize e+3*OneUnit.copies τ := by
  let k := OneUnit.copies τ
  have hk : 0 < k := by unfold k OneUnit.copies; omega
  have hp : ordinalHeadFree (.add e .one) = false := by rw [free_add,he] <;> rfl
  obtain ⟨hf,hs⟩ := repeatedActiveSize p .scalarRepeat k hk (.add e .one) hp
  have hact : ordinalHeadFree (.add (repeated p .scalarRepeat k (.add e .one)) e) = false := by
    rw [free_add,hf,he] <;> rfl
  change ordinalPartialSize (.add (repeated p .scalarRepeat k (.add e .one)) e) =
    (k+1)*ordinalPartialSize e+3*k
  rw [size_add_active _ _ hact,hs,size_add_active e .one hp]
  change k*(ordinalPartialSize e+1+1)+(k-1)+ordinalPartialSize e+1 =
    (k+1)*ordinalPartialSize e+3*k
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
  omega

private theorem unusedCoordinateSize (p : Policy) {Γ : List Ty} {σ : Ty} {m : Nat}
    (h : OrdinalVector (σ :: Γ) m) (j : Fin (m+1)) :
    ordinalPartialSize (h j) ≤ ordinalPartialSize
      (unusedVector p h ⟨j.val,by have := j.isLt; omega⟩) := by
  simp only [unusedVector,dif_pos j.isLt]
  exact size_add_ge_right _ _

private theorem unusedScalarStrict (p : Policy) {Γ : List Ty} {σ τ : Ty}
    (h : OrdinalVector (σ :: Γ) τ.level) (hf : ordinalHeadFree (h 0) = false) :
    ordinalPartialSize (h 0) < ordinalPartialSize (unusedVector p h 0) := by
  change ordinalPartialSize (h 0) < ordinalPartialSize (inflated p τ (h 0))
  rw [inflatedSize p _ hf]
  have hk : 0 < OneUnit.copies τ := by unfold OneUnit.copies; omega
  unfold OneUnit.coefficient
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem literalInflation : CurrentOneUnitTargets.LiteralInflation := by
  intro p Γ σ τ a
  obtain ⟨h,hh,_⟩ := actualAdmissibleAssignmentGenerated (σ :: Γ) τ p a
  let h' := unusedVector p h
  have hu : assignment p (OneUnit.unused a) = some h' := unused_assignment p a h hh
  let d : Coefficients := (OneUnit.multiplier h,OneUnit.multiplier h',ordinalHeadFree (h 0))
  have hd : typedCoefficients p a = some d := by
    unfold typedCoefficients
    rw [hh,hu] <;> rfl
  refine ⟨h,h',d,hh,hu,hd,rfl,multiplier_positive h,rfl,?_⟩
  intro hf
  change ordinalHeadFree (h 0) = false at hf
  refine ⟨inflatedSize p _ hf,fun j _ => unusedCoordinateSize p h j,?_⟩
  have hsum : ((List.ofFn h).map ordinalPartialSize).sum <
      ((List.ofFn h').map ordinalPartialSize).sum := by
    simp only [List.map_ofFn]
    exact sum_ofFn_strict_head (Nat.le_max_right 1 τ.level)
      (fun j => ordinalPartialSize (h j)) (fun j => ordinalPartialSize (h' j))
      (unusedCoordinateSize p h) (unusedScalarStrict p h hf)
  exact Nat.mul_lt_mul_of_pos_left hsum (Nat.pow_pos (by decide))

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
