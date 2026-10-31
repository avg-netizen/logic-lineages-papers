module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem abstractionNodePrim {α : Type*} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem consOptionsPrim : Primrec (fun p : Option (List Nat) × Option (List (List Nat)) => do
    let x ← p.1; let xs ← p.2; pure (x::xs)) := by
  apply Primrec.option_bind Primrec.fst
  change Primrec (fun p : (Option (List Nat) × Option (List (List Nat))) × List Nat => do
    let xs ← p.1.2; pure (p.2::xs))
  have h : Primrec (fun p : (Option (List Nat) × Option (List (List Nat))) × List Nat =>
      p.1.2.map (p.2 :: ·)) :=
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply h.of_eq
  intro p
  cases p.1.2 <;> rfl

private theorem collectPrim : Primrec collectLists := by
  have hs : Primrec₂ (fun (_ : List (Option (List Nat)))
      (p : Option (List Nat) × Option (List (List Nat))) => do
        let x ← p.1; let xs ← p.2; pure (x::xs)) := (consOptionsPrim.comp Primrec.snd).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const (some [])) hs
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, collectLists] at ih ⊢
    rw [ih]

private theorem partialsPrim :
    Primrec (fun p : Nat × Nat × List Nat => partialsCode p.1 p.2.1 p.2.2) := by
  have hl : Primrec (fun p : Nat × Nat × List Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun p : Nat × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun p : (Nat × Nat × List Nat) × Nat => p.1) := Primrec.fst
  have he := ordinalSyntaxPartialPrimitiveRecursive.comp
    ((hl.comp hp).pair (Primrec.snd.pair ((Primrec.list_getD 0).comp (hh.comp hp) Primrec.snd)))
  have h := collectPrim.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp hm)) he.to₂)
  exact h.of_eq (fun p => rfl)

private theorem sumPrim : Primrec (fun xs : List Nat => xs.sum) := by
  have h := Primrec.list_foldr (Primrec.id (α := List Nat)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem resultPrim :
    Primrec (fun p : Nat × Nat × List Nat × List (List Nat) =>
      abstractionResult p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hl : Primrec (fun p : Nat × Nat × List Nat × List (List Nat) => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × List Nat × List (List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun p : Nat × Nat × List Nat × List (List Nat) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × Nat × List Nat × List (List Nat) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hsum := sumPrim.comp (Primrec.list_map hh
    (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.2.comp Primrec.snd).to₂)
  have hfactor := Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) (Primrec.succ.comp hl)) hsum
  have hp : Primrec (fun p : (Nat × Nat × List Nat × List (List Nat)) × Nat => p.1) := Primrec.fst
  have hhead := ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp
    ((Primrec.list_getD 0).comp (hh.comp hp) Primrec.snd)
  have hzero := ordinalSyntaxSumOperationsPrimitiveRecursive.2.comp (hfactor.comp hp)
    ((Primrec.list_getD 0).comp
      ((Primrec.list_getD []).comp (hs.comp hp) (Primrec.const 0)) (Primrec.const 0))
  have hcol : Primrec (fun p : (Nat × Nat × List Nat × List (List Nat)) × Nat =>
      p.1.2.2.2.map (fun row => row.getD p.2 0)) :=
    Primrec.list_map (hs.comp hp)
      ((Primrec.list_getD 0).comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have hpositive := ordinalSyntaxSumOperationsPrimitiveRecursive.1.comp (hm.comp hp) hcol
  have hdelta := Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) hzero
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd
      (Primrec.nat_add.comp (hl.comp hp) (Primrec.const 2))) hpositive hhead)
  have hentry := Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.succ.comp (hm.comp hp)))
    (abstractionNodePrim (Primrec.const 4) hdelta hhead) hdelta
  have h := Primrec.list_map (Primrec.list_range.comp
    (Primrec.succ.comp (Primrec.nat_max.comp (Primrec.succ.comp hl) hm))) hentry.to₂
  exact h.of_eq (fun p => rfl)

theorem ordinalSyntaxAbstractionPrimitiveRecursive : Targets.OrdinalSyntaxAbstractionPrimitiveRecursive := by
  have hp : Primrec (fun p : (Nat × Nat × List Nat) × List (List Nat) => p.1) := Primrec.fst
  have hl := Primrec.fst.comp hp
  have hm := Primrec.fst.comp (Primrec.snd.comp hp)
  have hh := Primrec.snd.comp (Primrec.snd.comp hp)
  have hf := resultPrim.comp (hl.pair (hm.pair (hh.pair Primrec.snd)))
  have h := Primrec.option_map partialsPrim hf.to₂
  exact h.of_eq (fun p => rfl)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
