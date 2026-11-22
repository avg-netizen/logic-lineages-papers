module
public import LogicLineages.PermittedControl.AffineCollapseGuardedLowTargets
import LogicLineages.PermittedControl.AffineCollapseGuardRowsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardedLow
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

private theorem appendAll (f θ : Nat → Nat) (rows more : List Row)
    (xs ys : Snapshot) (hx : actualRows f θ rows xs) (hy : actualRows f θ more ys) :
    actualRows f θ (rows ++ more) (xs ++ ys) := by
  induction rows generalizing xs with
  | nil =>
      cases xs with
      | nil => exact hy
      | cons x xs => exact False.elim hx
  | cons row rows ih =>
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
          exact ⟨hx.1,hx.2.1,hx.2.2.1,ih xs hx.2.2.2⟩

private theorem splitAll (f θ : Nat → Nat) (rows more : List Row)
    (xs ys : Snapshot) (sameLength : rows.length = xs.length)
    (h : actualRows f θ (rows ++ more) (xs ++ ys)) :
    actualRows f θ rows xs ∧ actualRows f θ more ys := by
  induction rows generalizing xs with
  | nil =>
      cases xs with
      | nil => exact ⟨trivial,h⟩
      | cons x xs => simp at sameLength
  | cons row rows ih =>
      cases xs with
      | nil => simp at sameLength
      | cons x xs =>
          have req : rows.length = xs.length := Nat.succ.inj sameLength
          obtain ⟨h₁,h₂⟩ := ih xs req h.2.2.2
          exact ⟨⟨h.1,h.2.1,h.2.2.1,h₁⟩,h₂⟩

theorem exactFinitePairLow : ExactFinitePairLow := by
  intro f ρ prior lam hlim e input output rank bound testRows test positive
  let rows := AffineCollapseGuardRows.guardRows lam e input output
  let pass : (Nat → Nat) → Snapshot → Prop := fun θ values =>
    ∃ testValues : Snapshot, values = originalGuardSnapshot lam input θ ++ testValues ∧
      OriginalTestAt test positive θ testValues
  have iffRows (θ : Nat → Nat) :=
    AffineCollapseGuardRows.exactAffineCollapseGuardRows f lam hlim e input output θ
      (originalGuardSnapshot lam input θ)
  have shape (θ : Nat → Nat) : AffineCollapseGuardRows.trueSnapshot (originalGuardSnapshot lam input θ) :=
    ⟨0,(θ input : Int) - (actualOrdinalNorm lam.1.repr : Int),0,rfl⟩
  have lengths (θ : Nat → Nat) : rows.length = (originalGuardSnapshot lam input θ).length := rfl
  have low := HeterogeneousSignedMatrixLowStrips.exactGuardedLowExistential
    f ρ prior rank bound (rows ++ testRows) pass true
  constructor
  · rintro ⟨a,within,pr,graph,values,actual,holds⟩
    let θ := Function.update ρ rank a
    have hGuard : actualRows f θ rows (originalGuardSnapshot lam input θ) :=
      ((iffRows θ).mpr ⟨graph,rfl⟩).1
    have hRows := appendAll f θ rows testRows _ _ hGuard actual
    obtain ⟨branch,residual,member,hit,pr',snapshot,hSnap,hPass⟩ :=
      low.mp ⟨a,within,pr,_,hRows,⟨values,rfl,holds⟩⟩
    obtain ⟨values',rfl,hHolds⟩ := hPass
    exact ⟨branch,residual,member,hit,pr',values',hSnap,hHolds⟩
  · rintro ⟨branch,residual,member,hit,pr,values,actual,holds⟩
    obtain ⟨a,within,pr',snap,hSnap,hPass⟩ :=
      low.mpr ⟨branch,residual,member,hit,pr,_,actual,⟨values,rfl,holds⟩⟩
    let θ := Function.update ρ rank a
    obtain ⟨values',rfl,hHolds⟩ := hPass
    obtain ⟨hGuard,hTest⟩ := splitAll f θ rows testRows _ _ (lengths θ) hSnap
    exact ⟨a,within,pr',((iffRows θ).mp ⟨hGuard,shape θ⟩).1,values',hTest,hHolds⟩

end LogicLineages.PermittedControl.AffineCollapseGuardedLow
