module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionTargets
public import LogicLineages.StandardControlCurrent.PolicyPartialRunPrograms
public import LogicLineages.StandardControlCurrent.ComputableFoldProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAbstractionBasePrograms
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
theorem consOptionsPrim : Primrec (fun p : Option (List Nat) × Option (List (List Nat)) => do
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

theorem collectPrim : Primrec collectLists := by
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

theorem sumPrim : Primrec (fun xs : List Nat => xs.sum) := by
  have h := Primrec.list_foldr (Primrec.id (α := List Nat)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [ih]


theorem mapProgram {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {xs : α → List β} {g : α → β → γ} (hx : Computable xs)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (xs a).map (g a)) := by
  have h := ComputableFoldProof.filterMapProgram hx (Computable.option_some.comp hg)
  exact h.of_eq (fun a => by simp)

theorem factor : Primrec (fun x : Nat × List Nat => PolicyAbstraction.factorCode x.1 x.2) := by
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst))
    (sumPrim.comp (Primrec.list_map Primrec.snd
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.2.comp Primrec.snd).to₂))

theorem partials (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × List Nat => PolicyAbstraction.partialsCode p x.1 x.2.1 x.2.2) := by
  have he : Computable (fun x : (Nat × Nat × List Nat) × Nat =>
      PolicyPartial.run p x.1.1 x.2 (x.1.2.2.getD x.2 0)) :=
    Computable.comp (f := fun q : Nat × Nat × Nat => PolicyPartial.run p q.1 q.2.1 q.2.2)
      (g := fun x : (Nat × Nat × List Nat) × Nat => (x.1.1,x.2,x.1.2.2.getD x.2 0))
      (PolicyPartialRunPrograms.run p hp)
      ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair ((Primrec.list_getD 0).to_comp.comp
          (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd)))
  exact collectPrim.to_comp.comp (mapProgram
    (Primrec.list_range.to_comp.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))) he)
end LogicLineages.StandardControlCurrent.PolicyAbstractionBasePrograms
