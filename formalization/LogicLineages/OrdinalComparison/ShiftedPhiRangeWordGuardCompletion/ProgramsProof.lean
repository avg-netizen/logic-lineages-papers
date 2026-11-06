module
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterRangeWordGuardCompletion

theorem scalarTail_primitive : Primrec (fun p : Int × Int => scalarTail p.1 p.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst)
      (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.snd)) (Primrec.const 1)

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Letter × Int × Int =>
      ShiftedPhiRangeWordGuardCompletion.guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Word × Word × Letter × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hj := Primrec.fst.comp hr3
  have hk := Primrec.snd.comp hr3
  have hT := scalarTail_primitive.comp (hj.pair hk)
  have hP := CounterRangeWordGuardCompletion.Proof.rangeInputWord_primitive.comp (hB.pair ha)
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hA.pair hT))
    (Primrec.nat_max.comp
      (WordGuardCompletion.Proof.reachTail_primitive.comp (hP.pair hT))
      (WordGuardCompletion.Proof.reachTail_primitive.comp
        (hB.pair (RangePhiFactorization.Proof.factorTail_primitive.comp ha))))

theorem guardPrograms : Targets.GuardPrograms := ⟨scalarTail_primitive,guardTail_primitive⟩

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof
