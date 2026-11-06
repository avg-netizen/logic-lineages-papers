module
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.RangePhiFactorization.ProgramsProof
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedElementaryProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

theorem scalarTail_primitive : Primrec
    (fun p : Nat × Nat × Nat × Int × Int × Int × Int =>
      scalarTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let P := Nat × Nat × Nat × Int × Int × Int × Int
  have hd : Primrec (fun p : P => p.1) := Primrec.fst
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have he := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hj := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hk := Primrec.fst.comp hr4
  have hr5 := Primrec.snd.comp hr4
  have ha := Primrec.fst.comp hr5
  have hb := Primrec.snd.comp hr5
  have hjPred : Primrec (fun p : P => p.2.2.2.1 - 1) := by
    simpa only [sub_eq_add_neg] using
      (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp hj
        (Primrec.const (-1 : Int)) : Primrec (fun p : P => p.2.2.2.1 + (-1)))
  have hkPred : Primrec (fun p : P => p.2.2.2.2.1 - 1) := by
    simpa only [sub_eq_add_neg] using
      (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp hk
        (Primrec.const (-1 : Int)) : Primrec (fun p : P => p.2.2.2.2.1 + (-1)))
  have hleft : Primrec (fun p : P => kernelLetter p.1 p.2.1 p.2.2.2.1) :=
    (Primrec.const 3).pair (hd.pair (hc.pair hj))
  have hright : Primrec (fun p : P => kernelLetter p.1 p.2.2.1 p.2.2.2.2.1) :=
    (Primrec.const 3).pair (hd.pair (he.pair hk))
  have hequality := Focused.uniformTailPrograms.2.2.comp
    (hd.pair (hc.pair (he.pair (hjPred.pair hkPred))))
  exact Primrec.nat_max.comp hequality
    (Primrec.nat_max.comp
      (RangePhiFactorization.Proof.factorTail_primitive.comp hleft)
      (Primrec.nat_max.comp
        (RangePhiFactorization.Proof.factorTail_primitive.comp hright)
        (ShiftedPhiRangeWordGuardCompletion.Proof.scalarTail_primitive.comp (ha.pair hb))))

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Nat × Nat × Nat × Int × Int × Int × Int =>
      guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Nat × Int × Int × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hT := scalarTail_primitive.comp (Primrec.snd.comp Primrec.snd :
    Primrec (fun p : P => p.2.2))
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hA.pair hT))
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hB.pair hT))

theorem guardPrograms : Targets.GuardPrograms := ⟨scalarTail_primitive,guardTail_primitive⟩

end LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
