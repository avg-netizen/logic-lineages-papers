module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.Targets
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
open PolynomialGraphCompletion WordGuardCompletion

private theorem kernelLetter_primitive {α : Type} [Primcodable α]
    {d c : α → Nat} {j : α → Int}
    (hd : Primrec d) (hc : Primrec c) (hj : Primrec j) :
    Primrec (fun p => kernelLetter (d p) (c p) (j p)) :=
  (Primrec.const 3).pair (hd.pair (hc.pair hj))

theorem exposurePrefix_primitive :
    Primrec (fun p : Nat × Nat × Nat => exposurePrefix p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hm : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd := Primrec.nat_add.comp hn (Primrec.const 3)
  have hseed : Primrec (fun p : P => [kernelLetter (p.1+3) (p.2.2+(p.1+3)) 0]) :=
    Primrec.list_cons.comp
      (kernelLetter_primitive hd (Primrec.nat_add.comp hc hd) (Primrec.const (0 : Int)))
      (Primrec.const [])
  have hstep : Primrec (fun p : P × (Nat × Word) =>
      kernelLetter (p.1.1+p.2.1+4) (p.1.2.2+(p.1.1+p.2.1+4)) 0 :: p.2.2) := by
    have hdegree : Primrec (fun p : P × (Nat × Word) => p.1.1+p.2.1+4) :=
      Primrec.nat_add.comp
      (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.const 4)
    exact Primrec.list_cons.comp
      (kernelLetter_primitive hdegree
        (Primrec.nat_add.comp (hc.comp Primrec.fst) hdegree) (Primrec.const (0 : Int)))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.nat_rec' hm hseed hstep.to₂).of_eq
  intro p
  rcases p with ⟨n,m,c⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    change kernelLetter (n+m+4) (c+(n+m+4)) 0 ::
      (Nat.rec [kernelLetter (n+3) (c+(n+3)) 0]
        (fun i w => kernelLetter (n+i+4) (c+(n+i+4)) 0 :: w) m) = _
    rw [ih]
    rfl

theorem exposureWord_primitive :
    Primrec (fun p : Nat × Nat × Nat × Int =>
      exposureWord p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Nat × Nat × Nat × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hm : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hparams : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc := Primrec.fst.comp hparams
  have hj := Primrec.snd.comp hparams
  exact Primrec.list_append.comp
    (exposurePrefix_primitive.comp (hn.pair (hm.pair hc)))
    (Primrec.list_cons.comp
      (SourceRangeExpansion.Proof.lowerHead_primitive.comp (hn.pair (hc.pair hj)))
      (Primrec.const []))

theorem exposureTail_primitive :
    Primrec (fun p : Nat × Nat × Nat × Int =>
      exposureTail p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Nat × Nat × Nat × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hm : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hparams : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc := Primrec.fst.comp hparams
  have hj := Primrec.snd.comp hparams
  have hseed : Primrec (fun p : P =>
      SourceRangeExpansion.expansionTail p.1 p.2.2.1 p.2.2.2) :=
    SourceRangeExpansion.Proof.expansionTail_primitive.comp (hn.pair (hc.pair hj))
  have hstep : Primrec (fun p : P × (Nat × Nat) =>
      max (SourceRangeExpansion.expansionTail (p.1.1+p.2.1+1) p.1.2.2.1 p.1.2.2.2)
        p.2.2) := by
    have hrank : Primrec (fun p : P × (Nat × Nat) => p.1.1+p.2.1+1) :=
      Primrec.nat_add.comp
      (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.const 1)
    exact Primrec.nat_max.comp
      (SourceRangeExpansion.Proof.expansionTail_primitive.comp
        (hrank.pair ((hc.comp Primrec.fst).pair (hj.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.nat_rec' hm hseed hstep.to₂).of_eq
  intro p
  rcases p with ⟨n,m,c,j⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    change max (SourceRangeExpansion.expansionTail (n+m+1) c j)
      (Nat.rec (SourceRangeExpansion.expansionTail n c j)
        (fun i t => max (SourceRangeExpansion.expansionTail (n+i+1) c j) t) m) = _
    rw [ih]
    rfl

theorem contextTail_primitive :
    Primrec (fun p : Word × Word × Nat × Nat × Nat × Int =>
      contextTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Nat × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hS : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hrest
  have hgap := Primrec.snd.comp hrest
  have hm := Primrec.fst.comp hgap
  have hparams := Primrec.snd.comp hgap
  have hc := Primrec.fst.comp hparams
  have hj := Primrec.snd.comp hparams
  have hd := Primrec.nat_add.comp (Primrec.nat_add.comp hn hm) (Primrec.const 3)
  have hhead := kernelLetter_primitive hd hc hj
  have hsingle := Primrec.list_cons.comp hhead (Primrec.const [])
  have horiginal : Primrec (fun p : P =>
      p.1++[kernelLetter (p.2.2.1+p.2.2.2.1+3) p.2.2.2.2.1 p.2.2.2.2.2]++p.2.1) := by
    apply (Primrec.list_append.comp (Primrec.list_append.comp hA hsingle) hS).of_eq
    intro p
    simp only [List.append_assoc]
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (hA.pair (exposureTail_primitive.comp hrest)))
    (WordGuardCompletion.Proof.wordTail_primitive.comp horiginal)

theorem exposurePrograms : Targets.ExposurePrograms :=
  ⟨exposurePrefix_primitive,exposureWord_primitive,exposureTail_primitive,contextTail_primitive⟩

end LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
