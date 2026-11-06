module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.CounterSourceTheoremProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

private theorem kernelLetter_primitive {α : Type} [Primcodable α]
    {d c : α → Nat} (hd : Primrec d) (hc : Primrec c) :
    Primrec (fun p => kernelLetter (d p) (c p) 0) :=
  (Primrec.const 3).pair (hd.pair (hc.pair (Primrec.const (0 : Int))))

theorem leaderWord_primitive : Primrec (fun p : Nat × Nat => leaderWord p.1 p.2) := by
  have hseed : Primrec (fun p : Nat × Nat => [kernelLetter 3 (p.2+3) 0]) :=
    Primrec.list_cons.comp
      (kernelLetter_primitive (Primrec.const 3)
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 3))) (Primrec.const [])
  have hstep : Primrec (fun p : (Nat × Nat) × (Nat × Word) =>
      kernelLetter (p.2.1+4) (p.1.2+p.2.1+4) 0 :: p.2.2) :=
    Primrec.list_cons.comp
      (kernelLetter_primitive
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 4))
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
            (Primrec.fst.comp Primrec.snd)) (Primrec.const 4)))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.nat_rec' Primrec.fst hseed hstep.to₂).of_eq
  intro p
  rcases p with ⟨n,c⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change kernelLetter (n+4) (c+n+4) 0 ::
      (Nat.rec [kernelLetter 3 (c+3) 0]
        (fun i w => kernelLetter (i+4) (c+i+4) 0 :: w) n) = _
    rw [ih]
    rfl

theorem leaderTail_primitive : Primrec (fun p : Nat × Nat => leaderTail p.1 p.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.snd
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.fst (Primrec.const 3)))) (Primrec.const 1))
    (WordGuardCompletion.Proof.wordTail_primitive.comp leaderWord_primitive)

theorem scalarTail_primitive : Primrec (fun p : Nat × Nat × Nat × Int × Int =>
    scalarTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Nat × Nat × Nat × Int × Int
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : P => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ha := Primrec.nat_add.comp
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp hj)
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp hk)
  exact Primrec.nat_max.comp
    (CounterSourceTheorem.Proof.uniformTailPrograms.2.2.comp
      (hn.pair (hc.pair (he.pair ha))))
    (Primrec.nat_max.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp hc (Primrec.nat_add.comp hn (Primrec.const 3)))
        (Primrec.const 1))
      (leaderTail_primitive.comp (hn.pair hc)))

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Nat × Nat × Nat × Nat × Int × Int =>
      guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Nat × Nat × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hrest
  have hr3 := Primrec.snd.comp hrest
  have hm := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hc := Primrec.fst.comp hr4
  have hr5 := Primrec.snd.comp hr4
  have he := Primrec.fst.comp hr5
  have hr6 := Primrec.snd.comp hr5
  have hj := Primrec.fst.comp hr6
  have hk := Primrec.snd.comp hr6
  have hleft := scalarTail_primitive.comp (hn.pair (hc.pair (he.pair (hj.pair hk))))
  have hright := scalarTail_primitive.comp (hm.pair (he.pair (hc.pair (hk.pair hj))))
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hA.pair hleft))
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hB.pair hright))

theorem guardPrograms : Targets.GuardPrograms :=
  ⟨leaderWord_primitive, leaderTail_primitive, scalarTail_primitive, guardTail_primitive⟩

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
