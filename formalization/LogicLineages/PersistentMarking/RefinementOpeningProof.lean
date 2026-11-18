import LogicLineages.PersistentMarking.RefinementOpeningTargets
import LogicLineages.PersistentMarking.RefinementRenamingProof
namespace LogicLineages.PersistentMarking.RefinementOpeningProof
open Spine NameBridge RefinementMeasure RefinementRenamingTargets RefinementRenameSupport

def swapNat (x y n : Nat) : Nat := if n=x then y else if n=y then x else n

theorem swapInvolution (x y n : Nat) : swapNat x y (swapNat x y n) = n := by
  by_cases hx : n=x
  · subst n; by_cases he : x=y <;> simp_all [swapNat]
  · by_cases hy : n=y
    · subst n; simp_all [swapNat]
    · simp [swapNat,hx,hy]

def swap (σ : Ty) (x y : Nat) : NameRenaming := fun τ n => if τ=σ then swapNat x y n else n

theorem swapInjective (σ : Ty) (x y : Nat) : injectiveNames (swap σ x y) := by
  intro τ a b h
  by_cases ht : τ=σ
  · simp only [swap,ht,if_true] at h
    have hh := congrArg (swapNat x y) h
    simpa only [swapInvolution] using hh
  · simpa only [swap,ht,if_false] using h

theorem swapName (σ : Ty) (x y : Nat) : swap σ x y σ x = y := by simp [swap,swapNat]

mutual
 theorem absent (σ : Ty) (x y : Nat) (q : Expr)
    (hx : freeOccurs (σ,x) q = false) (hy : freeOccurs (σ,y) q = false) : rename (swap σ x y) q = q := by
  cases q with
  | free τ n =>
    have hnx : (σ,x) ≠ (τ,n) := by simpa only [freeOccurs,decide_eq_false_iff_not] using hx
    have hny : (σ,y) ≠ (τ,n) := by simpa only [freeOccurs,decide_eq_false_iff_not] using hy
    by_cases ht : τ=σ
    · subst τ
      have hn : n ≠ x := by intro h; subst n; exact hnx rfl
      have hm : n ≠ y := by intro h; subst n; exact hny rfl
      simp [RefinementRenameSupport.renameFree,swap,swapNat,hn,hm]
    · simp [RefinementRenameSupport.renameFree,swap,ht]
  | bound τ i => rfl
  | lam τ q => simpa only [renameLam] using congrArg (Expr.lam τ) (absent σ x y q hx hy)
  | head f qs => exact congrArg (Expr.head f) (absentArgs σ x y qs hx hy)
  | marked f τ qs es =>
    have hx' : freeOccursArgs (σ,x) qs = false ∧ freeOccursArgs (σ,x) es = false := by simpa only [freeOccurs,Bool.or_eq_false_iff] using hx
    have hy' : freeOccursArgs (σ,y) qs = false ∧ freeOccursArgs (σ,y) es = false := by simpa only [freeOccurs,Bool.or_eq_false_iff] using hy
    change Expr.marked f τ (renameArgs _ qs) (renameArgs _ es) = Expr.marked f τ qs es
    exact congr (congrArg (Expr.marked f τ) (absentArgs σ x y qs hx'.1 hy'.1)) (absentArgs σ x y es hx'.2 hy'.2)
 termination_by sizeOf q
 theorem absentArgs (σ : Ty) (x y : Nat) (qs : Args)
    (hx : freeOccursArgs (σ,x) qs = false) (hy : freeOccursArgs (σ,y) qs = false) : renameArgs (swap σ x y) qs = qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hx' : freeOccurs (σ,x) q = false ∧ freeOccursArgs (σ,x) qs = false := by simpa only [freeOccursArgs,Bool.or_eq_false_iff] using hx
    have hy' : freeOccurs (σ,y) q = false ∧ freeOccursArgs (σ,y) qs = false := by simpa only [freeOccursArgs,Bool.or_eq_false_iff] using hy
    change Args.cons (rename _ q) (renameArgs _ qs) = Args.cons q qs
    exact congr (congrArg Args.cons (absent σ x y q hx'.1 hy'.1)) (absentArgs σ x y qs hx'.2 hy'.2)
 termination_by sizeOf qs
end

theorem opened (σ : Ty) (x y : Nat) (q : Expr)
    (hx : freeOccurs (σ,x) q = false) (hy : freeOccurs (σ,y) q = false) :
    rename (swap σ x y) (openBody σ x q) = openBody σ y q := by
  rw [opening,swapName,absent σ x y q hx hy]

theorem synchronize : RefinementOpeningTargets.Synchronize := by
  intro S σ x y q s hxq hxs hyq hys h
  obtain ⟨h0,he0⟩ := RefinementRenamingProof.tree S (swap σ x y) (swapInjective σ x y) _ _ h
  obtain ⟨h',he⟩ := RefinementRenamingProof.transport (opened σ x y q hxq hyq) (opened σ x y s hxs hys) h0
  exact ⟨h',he.trans he0⟩
end LogicLineages.PersistentMarking.RefinementOpeningProof
