module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem atomConsPrim : Primrec (fun p : Option Nat × Option (List Nat) => do
    let x ← p.1; let xs ← p.2; pure (x::xs)) := by
  apply Primrec.option_bind Primrec.fst
  change Primrec (fun p : (Option Nat × Option (List Nat)) × Nat => do
    let xs ← p.1.2; pure (p.2::xs))
  have h : Primrec (fun p : (Option Nat × Option (List Nat)) × Nat => p.1.2.map (p.2 :: ·)) :=
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply h.of_eq
  intro p
  cases p.1.2 <;> rfl

private theorem collectAtomsPrim : Primrec collectAtoms := by
  have hs : Primrec₂ (fun (_ : List (Option Nat)) (p : Option Nat × Option (List Nat)) => do
    let x ← p.1; let xs ← p.2; pure (x::xs)) := (atomConsPrim.comp Primrec.snd).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const (some [])) hs
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons, collectAtoms] at ih ⊢
    rw [ih]

private theorem vectorConsPrim : Primrec (fun p : Nat × List Nat => do
    let s ← (extraction p.1).2
    let ps ← collectAtoms (p.2.map (fun n => (extraction n).1))
    pure (s, ps)) := by
  have hscalar : Primrec (fun p : Nat × List Nat => (extraction p.1).2) :=
    Primrec.snd.comp (ordinalSyntaxExtractionPrimitiveRecursive.comp Primrec.fst)
  have hpositive : Primrec (fun p : Nat × List Nat => collectAtoms (p.2.map (fun n => (extraction n).1))) :=
    collectAtomsPrim.comp (Primrec.list_map Primrec.snd
      (Primrec.fst.comp (ordinalSyntaxExtractionPrimitiveRecursive.comp Primrec.snd)).to₂)
  apply Primrec.option_bind hscalar
  change Primrec (fun p : (Nat × List Nat) × Nat => do
    let ps ← collectAtoms (p.1.2.map (fun n => (extraction n).1))
    pure (p.2, ps))
  have h : Primrec (fun p : (Nat × List Nat) × Nat =>
      (collectAtoms (p.1.2.map (fun n => (extraction n).1))).map (fun ps => (p.2, ps))) :=
    Primrec.option_map (hpositive.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  apply h.of_eq
  intro p
  cases collectAtoms (p.1.2.map (fun n => (extraction n).1)) <;> rfl

theorem ordinalSyntaxVectorCompilerPrimitiveRecursive : Targets.OrdinalSyntaxVectorCompilerPrimitiveRecursive := by
  have h := Primrec.list_casesOn (Primrec.id (α := List Nat)) (Primrec.const none)
    (vectorConsPrim.comp Primrec.snd).to₂
  apply h.of_eq
  intro xs
  cases xs <;> rfl
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
