module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem counterTail_primitive : Primrec
    (fun p : Nat × Nat × Nat => counterTail p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have hn : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hK : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd := Primrec.nat_add.comp hn (Primrec.const 3)
  have ht : Primrec (fun p : P => CounterLeaderBounds.threshold p.1 p.2.1) :=
    Primrec.nat_max.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp hc (Primrec.nat_mul.comp (Primrec.const 2) hd))
        (Primrec.const 1))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hc)
        (Primrec.const 10))
  exact Primrec.nat_max.comp ht
    (Primrec.nat_max.comp
      (CounterWordGuardCompletion.Proof.leaderTail_primitive.comp (hn.pair hc))
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp hc hd) (Primrec.const 1)) hK))

theorem rangeTail_primitive : Primrec rangeTail :=
  Primrec.nat_add.comp Primrec.id (Primrec.const 1)

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Nat × Nat × Int × Int =>
      guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hc := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hj := Primrec.fst.comp hr4
  have hk := Primrec.snd.comp hr4
  have hK := Primrec.nat_add.comp
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp hj)
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp hk)
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (hA.pair (counterTail_primitive.comp (hn.pair (hc.pair hK)))))
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (hB.pair (rangeTail_primitive.comp hK)))

theorem guardPrograms : Targets.GuardPrograms :=
  ⟨counterTail_primitive, rangeTail_primitive, guardTail_primitive⟩

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
