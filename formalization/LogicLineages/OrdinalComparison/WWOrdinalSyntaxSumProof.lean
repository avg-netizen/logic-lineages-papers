module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem prefix_congr (n : Nat) (a b : List Nat)
    (h : ∀ j ≤ n, a.getD j 0 = b.getD j 0) : sumPrefix n a = sumPrefix n b := by
  induction n with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    rw [sumPrefix, sumPrefix, ih (fun j hj => h j (by omega)), h (n+1) (by omega)]

private theorem lookup_ofFn {n : Nat} (f : Fin n → Nat) (j : Fin n) :
    (List.ofFn f).getD j.val 0 = f j := by
  simp [List.getD_eq_getElem?_getD, j.isLt]

theorem ordinalSyntaxSumCorrect : Targets.OrdinalSyntaxSumCorrect := by
  intro Γ n
  induction n with
  | zero => intro f; simp [sumPrefix, leftShape, AdmissibleSum.expand]
  | succ n ih =>
    intro f
    let g : Fin (n+1) → OrdinalExpression Γ := fun j => f (Fin.castAdd 1 j)
    have hp : sumPrefix n (List.ofFn (fun j => typedCode (f j))) =
        sumPrefix n (List.ofFn (fun j => typedCode (g j))) := by
      apply prefix_congr
      intro j hj
      have h1 : j < n+2 := by omega
      have h2 : j < n+1 := by omega
      rw [lookup_ofFn _ ⟨j,h1⟩, lookup_ofFn _ ⟨j,h2⟩]
      rfl
    rw [sumPrefix, hp, ih g]
    rw [lookup_ofFn _ ⟨n+1, by omega⟩]
    rfl

theorem ordinalSyntaxRepeatCorrect : Targets.OrdinalSyntaxRepeatCorrect := by
  intro Γ site count t
  cases count with
  | zero => rfl
  | succ n =>
    have h := ordinalSyntaxSumCorrect Γ n (fun _ => t)
    simpa [repeatCode, AdmissibleAssignment.repeated, allLeftPolicy, List.replicate_succ] using h

theorem ordinalSyntaxSumOperationsPrimitiveRecursive : Targets.OrdinalSyntaxSumOperationsPrimitiveRecursive := by
  have hbody : Primrec (fun p : List Nat × (Nat × Nat) => node 4 p.2.2 (p.1.getD (p.2.1+1) 0)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd)
        ((Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
      (Primrec.const 4)
  have hrec := Primrec.nat_rec ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0)) hbody.to₂
  have hs : Primrec₂ (fun xs : List Nat => fun n => sumPrefix n xs) := by
    apply hrec.of_eq
    intro xs n
    induction n with
    | zero => rfl
    | succ n ih => change node 4 (Nat.rec _ _ n) _ = _; rw [ih]; rfl
  have hsum : Primrec₂ sumPrefix := (hs.comp Primrec.snd Primrec.fst).to₂
  refine ⟨hsum, ?_⟩
  have hr : Primrec (fun p : Nat × Nat => List.replicate p.1 p.2) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (fun p : Nat × Nat => p.1)))
      (Primrec.snd.comp Primrec.fst).to₂
    apply h.of_eq
    intro p
    simp
  exact (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
    (hsum.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)) hr)).to₂
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
