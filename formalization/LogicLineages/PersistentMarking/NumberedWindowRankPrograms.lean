module
public import LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
public import Mathlib.Computability.Primrec.List
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRankPrograms
open NumberedWindowCopyAlgorithm
open NumberedWindowSyntaxShapePrograms (pairs anyOption)
open NumberedWindowPositivePathParserPrograms (equalPrim)

theorem lookupPrim (entries : Entries) : Primrec (lookup entries) := by
  induction entries with
  | nil => exact Primrec.const none
  | cons entry tail ih =>
    have later : Primrec (fun p : Nat × Nat => (p.1,p.2+1)) :=
      Primrec.fst.pair (Primrec.succ.comp Primrec.snd)
    exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const entry.1))
      (Primrec.const (some (entry.2,0))) ((Primrec.option_map₁ later).comp ih)

private theorem rankedPrim (xs : Entries) : Primrec (fun p : Nat × Nat =>
    (lookup xs p.1).bind (fun v => if p.2 = v.1 then some (v.2+2) else none)) := by
  let P := (Nat × Nat) × Nat × Nat
  have arity : Primrec (fun x : P => x.1.2) := Primrec.snd.comp Primrec.fst
  have declared : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have index : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.option_bind ((lookupPrim xs).comp Primrec.fst)
    (Primrec.ite (Primrec.eq.comp arity declared)
      (Primrec.option_some.comp (Primrec.nat_add.comp index (Primrec.const 2))) (Primrec.const none)).to₂

theorem rankPrim (xs : Entries) : Primrec (rank xs) := by
  let Node := Nat × Nat
  have tag : Primrec (Prod.fst : Node → Nat) := Primrec.fst
  have payload : Primrec (Prod.snd : Node → Nat) := Primrec.snd
  have ranked := (Primrec.option_bind₁ (rankedPrim xs)).comp (pairs.comp payload)
  have parts : Primrec (fun p : Node => rankParts xs p.1 p.2) :=
    Primrec.ite (Primrec.nat_lt.comp tag (Primrec.const 4)) (Primrec.const (some 1))
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 4)) (Primrec.const (some 0))
        (Primrec.ite (Primrec.eq.comp tag (Primrec.const 5)) ranked (Primrec.const none)))
  exact (Primrec.option_bind₁ parts).comp pairs

theorem comparePrim (small : Bool) (xs : Entries) : Primrec₂ (compareRanks small xs) := by
  let P := ((Nat × Nat) × Nat) × Nat
  have m : Primrec (fun x : P => x.1.2) := Primrec.snd.comp Primrec.fst
  have n : Primrec (fun x : P => x.2) := Primrec.snd
  have test : Primrec (fun x : P => if small then decide (x.2 < x.1.2) else decide (x.1.2 = x.2)) := by
    cases small with
    | true => exact (Primrec.nat_lt.comp n m).decide
    | false => exact (Primrec.eq.comp m n).decide
  exact anyOption ((rankPrim xs).comp Primrec.fst)
    (anyOption ((rankPrim xs).comp (Primrec.snd.comp Primrec.fst)) test.to₂).to₂

private theorem inHeads (heads : List Nat) : Primrec (heads.contains ·) := by
  have mem : PrimrecRel (fun (xs : List Nat) (n : Nat) => n ∈ xs) :=
    (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)).exists_mem_list.of_eq (by simp)
  apply ((mem.comp (Primrec.const heads) Primrec.id).decide).of_eq
  intro n
  apply Bool.eq_iff_iff.mpr
  simp

theorem allowedPrim {α} [Primcodable α] (small : Bool) (xs : Entries) (heads : List Nat)
    {t f g : α → Nat} (ht : Primrec t) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => allowedTarget small xs heads (t x) (f x) (g x)) :=
  Primrec.and.comp (Primrec.and.comp (equalPrim.comp ht
    (Primrec.fst.comp (NumberedWindowHeadDeclarationPrograms.declarationPrim.comp hg)))
    ((comparePrim small xs).comp hf hg)) ((inHeads heads).comp hg)
end LogicLineages.PersistentMarking.NumberedWindowRankPrograms
