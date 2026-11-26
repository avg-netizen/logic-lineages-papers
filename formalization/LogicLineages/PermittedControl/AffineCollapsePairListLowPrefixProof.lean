module
public import LogicLineages.PermittedControl.AffineCollapsePairListLowTargets
import LogicLineages.PermittedControl.AffineCollapseGuardRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapsePairListLow
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open AffineCollapseGuardedLow (originalGuardSnapshot)

theorem actualRowsAppend (f θ : Nat → Nat) (rows more : List Row)
    (xs ys : Snapshot) (len : rows.length = xs.length) :
    actualRows f θ (rows ++ more) (xs ++ ys) ↔
      actualRows f θ rows xs ∧ actualRows f θ more ys := by
  induction rows generalizing xs with
  | nil =>
      cases xs with
      | nil => simp [actualRows]
      | cons x xs => simp at len
  | cons row rows ih =>
      cases xs with
      | nil => simp at len
      | cons x xs =>
          have req : rows.length = xs.length := Nat.succ.inj len
          constructor
          · intro h
            obtain ⟨h₁,h₂⟩ := (ih xs req).mp h.2.2.2
            exact ⟨⟨h.1,h.2.1,h.2.2.1,h₁⟩,h₂⟩
          · rintro ⟨h₁,h₂⟩
            exact ⟨h₁.1,h₁.2.1,h₁.2.2.1,(ih xs req).mpr ⟨h₁.2.2.2,h₂⟩⟩

theorem prefixLength (θ : Nat → Nat) (pairs : List Pair) :
    (prefixRows pairs).length = (prefixSnapshot θ pairs).length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
      have head : (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2).length =
          (originalGuardSnapshot p.1 p.2.2.1 θ).length := rfl
      simp only [prefixRows,prefixSnapshot,List.foldr_cons,List.length_append]
      change (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2).length +
        (prefixRows ps).length = (originalGuardSnapshot p.1 p.2.2.1 θ).length +
          (prefixSnapshot θ ps).length
      rw [head]
      exact congrArg (fun n => (originalGuardSnapshot p.1 p.2.2.1 θ).length + n) ih

private theorem actualHead (f θ : Nat → Nat) (p : Pair) (hlim : Order.IsSuccLimit p.1.1.repr) :
    actualRows f θ (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2)
      (originalGuardSnapshot p.1 p.2.2.1 θ) ↔
      AffineCollapseGraphComposition.graph f (rawNoteEncode p.1.1) p.2.1 p.2.2.1 p.2.2.2 θ := by
  have h := AffineCollapseGuardRows.exactAffineCollapseGuardRows f p.1 hlim
    p.2.1 p.2.2.1 p.2.2.2 θ (originalGuardSnapshot p.1 p.2.2.1 θ)
  have truePrefix : AffineCollapseGuardRows.trueSnapshot (originalGuardSnapshot p.1 p.2.2.1 θ) :=
    ⟨0,(θ p.2.2.1 : Int)-(actualOrdinalNorm p.1.1.repr : Int),0,rfl⟩
  exact ⟨fun ht => (h.mp ⟨ht,truePrefix⟩).1, fun hg => (h.mpr ⟨hg,rfl⟩).1⟩

theorem exactSharedPrefix : ExactSharedPrefix := by
  intro f θ pairs
  induction pairs with
  | nil => simp [prefixRows,prefixSnapshot,actualRows,GraphsAt]
  | cons p ps ih =>
      intro lim
      have hp := lim p (List.mem_cons_self)
      have hs : LimitHeads ps := fun q hq => lim q (List.mem_cons_of_mem _ hq)
      have app := actualRowsAppend f θ
        (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2) (prefixRows ps)
        (originalGuardSnapshot p.1 p.2.2.1 θ) (prefixSnapshot θ ps) rfl
      constructor
      · intro h
        obtain ⟨h₁,h₂⟩ := app.mp h
        intro q hq
        rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact (actualHead f θ p hp).mp h₁
        · exact (ih hs).mp h₂ q hq
      · intro h
        exact app.mpr ⟨(actualHead f θ p hp).mpr (h p List.mem_cons_self),
          (ih hs).mpr (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

end LogicLineages.PermittedControl.AffineCollapsePairListLow
