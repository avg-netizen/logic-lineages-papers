module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.RangePhiFactorization.ProgramsProof
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem preimageWord_primitive : Primrec preimageWord :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) (Primrec.const [])
    (Primrec.list_cons.comp RangePhiFactorization.Proof.predecessorHead_primitive (Primrec.const []))

theorem rangeInputWord_primitive : Primrec (fun p : Word × Letter => rangeInputWord p.1 p.2) :=
  Primrec.list_append.comp Primrec.fst (preimageWord_primitive.comp Primrec.snd)

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Nat × Nat × Letter × Int × Int =>
      guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Letter × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hc := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have ha := Primrec.fst.comp hr4
  have hr5 := Primrec.snd.comp hr4
  have hj := Primrec.fst.comp hr5
  have hk := Primrec.snd.comp hr5
  have hInput := rangeInputWord_primitive.comp (hB.pair ha)
  exact Primrec.nat_max.comp
    (CounterPhiWordGuardCompletion.Proof.guardTail_primitive.comp
      (hA.pair (hInput.pair (hn.pair (hc.pair (hj.pair hk))))))
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (hB.pair (RangePhiFactorization.Proof.factorTail_primitive.comp ha)))

theorem guardPrograms : Targets.GuardPrograms :=
  ⟨preimageWord_primitive,rangeInputWord_primitive,guardTail_primitive⟩

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
