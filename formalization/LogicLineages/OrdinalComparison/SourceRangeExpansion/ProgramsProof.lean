module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open LayeredComparison.IntegerAlgorithms.Proof

private theorem kernelLetter_primitive {α : Type} [Primcodable α]
    {d c : α → Nat} {j : α → Int}
    (hd : Primrec d) (hc : Primrec c) (hj : Primrec j) :
    Primrec (fun p => kernelLetter (d p) (c p) (j p)) :=
  (Primrec.const 3).pair (hd.pair (hc.pair hj))

private theorem quadraticLetter_primitive : Primrec quadraticLetter :=
  (Primrec.const 2).pair ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))

theorem lowerHead_primitive :
    Primrec (fun p : Nat × Nat × Int => lowerHead p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hhalf : Primrec (fun p : P => (((p.2.1+1)/2 : Nat) : Int)) :=
    ofNat_primitive.comp (Primrec.nat_div.comp
      (Primrec.nat_add.comp hc (Primrec.const 1)) (Primrec.const 2))
  have hindex : Primrec (fun p : P => p.2.2-(((p.2.1+1)/2 : Nat) : Int)) := by
    apply (add_primitive.comp hj (negate_primitive.comp hhalf)).of_eq
    intro p
    simp only [sub_eq_add_neg]
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0))
    (quadraticLetter_primitive.comp hindex)
    (kernelLetter_primitive (Primrec.nat_add.comp hn (Primrec.const 2)) hc hj)

theorem expansionWord_primitive :
    Primrec (fun p : Nat × Nat × Int => expansionWord p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd := Primrec.nat_add.comp hn (Primrec.const 3)
  exact Primrec.list_cons.comp
    (kernelLetter_primitive hd (Primrec.nat_add.comp hc hd) (Primrec.const (0 : Int)))
    (Primrec.list_cons.comp lowerHead_primitive (Primrec.const []))

private theorem finiteKernelRecursionThreshold_primitive :
    Primrec (fun p : Nat × Nat × Int => finiteKernelRecursionThreshold p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Int
  have hd : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_max.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp hc (Primrec.nat_mul.comp (Primrec.const 2) hd))
      (Primrec.const 1))
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp hc
        (Primrec.nat_mul.comp (Primrec.const 2) (abs_primitive.comp hj)))
      (Primrec.const 3))

theorem expansionTail_primitive :
    Primrec (fun p : Nat × Nat × Int => expansionTail p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd := Primrec.nat_add.comp hn (Primrec.const 3)
  exact Primrec.nat_max.comp
    (finiteKernelRecursionThreshold_primitive.comp (hd.pair (hc.pair hj)))
    (Primrec.nat_max.comp
      (WordGuardCompletion.Proof.letterTail_primitive.comp (kernelLetter_primitive hd hc hj))
      (WordGuardCompletion.Proof.wordTail_primitive.comp expansionWord_primitive))

theorem contextTail_primitive :
    Primrec (fun p : Word × Word × Nat × Nat × Int =>
      contextTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hS : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hrest
  have hparams := Primrec.snd.comp hrest
  have hc := Primrec.fst.comp hparams
  have hj := Primrec.snd.comp hparams
  have hhead := kernelLetter_primitive
    (Primrec.nat_add.comp hn (Primrec.const 3)) hc hj
  have hsingle := Primrec.list_cons.comp hhead (Primrec.const [])
  have horiginal : Primrec (fun p : P =>
      p.1++[kernelLetter (p.2.2.1+3) p.2.2.2.1 p.2.2.2.2]++p.2.1) := by
    apply (Primrec.list_append.comp (Primrec.list_append.comp hA hsingle) hS).of_eq
    intro p
    simp only [List.append_assoc]
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (hA.pair (expansionTail_primitive.comp hrest)))
    (WordGuardCompletion.Proof.wordTail_primitive.comp horiginal)

theorem expansionPrograms : Targets.ExpansionPrograms :=
  ⟨lowerHead_primitive,expansionWord_primitive,expansionTail_primitive,contextTail_primitive⟩

end LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
