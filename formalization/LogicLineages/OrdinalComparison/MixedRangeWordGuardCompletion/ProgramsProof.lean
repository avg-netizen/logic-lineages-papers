module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.ProgramsProof
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open LayeredComparison.IntegerAlgorithms.Proof

private theorem shiftLetter_primitive : Primrec shiftLetter :=
  (Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))

theorem retainedWord_primitive :
    Primrec (fun p : Word × Nat × Nat × Nat =>
      retainedWord p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Word × Nat × Nat × Nat
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hparams : Primrec (fun p : P => p.2) := Primrec.snd
  exact Primrec.list_append.comp hA
    (FiniteRangeExposure.Proof.exposurePrefix_primitive.comp hparams)

theorem kernelGuardTail_primitive :
    Primrec (fun p : Word × Word × Nat × Nat × Nat × Nat × Int × Int × Int × Int =>
      kernelGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Nat × Nat × Int × Int × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hm := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hc := Primrec.fst.comp hr4
  have hr5 := Primrec.snd.comp hr4
  have he := Primrec.fst.comp hr5
  have hr6 := Primrec.snd.comp hr5
  have hj := Primrec.fst.comp hr6
  have hr7 := Primrec.snd.comp hr6
  have hk := Primrec.fst.comp hr7
  have hr8 := Primrec.snd.comp hr7
  have ha := Primrec.fst.comp hr8
  have hb := Primrec.snd.comp hr8
  have hnSucc := Primrec.nat_add.comp hn (Primrec.const 1)
  have hd := Primrec.nat_add.comp hn (Primrec.const 3)
  have hS := Primrec.list_cons.comp (shiftLetter_primitive.comp ha) (Primrec.const [])
  have hcontext := FiniteRangeExposure.Proof.contextTail_primitive.comp
    (hA.pair (hS.pair (hnSucc.pair (hm.pair (hc.pair hj)))))
  have hretained := retainedWord_primitive.comp (hA.pair (hnSucc.pair (hm.pair hc)))
  have hguard := ShiftedEqualRankWordGuardCompletion.Proof.guardTail_primitive.comp
    (hretained.pair (hB.pair (hd.pair (hc.pair (he.pair (hj.pair (hk.pair (ha.pair hb))))))))
  exact Primrec.nat_max.comp hcontext hguard

theorem quadraticGuardTail_primitive :
    Primrec (fun p : Word × Word × Nat × Nat × Int × Int × Int × Int =>
      quadraticGuardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2) := by
  let P := Word × Word × Nat × Nat × Int × Int × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hm := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hc := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hj := Primrec.fst.comp hr4
  have hr5 := Primrec.snd.comp hr4
  have hk := Primrec.fst.comp hr5
  have hr6 := Primrec.snd.comp hr5
  have ha := Primrec.fst.comp hr6
  have hb := Primrec.snd.comp hr6
  have hhalf : Primrec (fun p : P => (((p.2.2.2.1+1)/2 : Nat) : Int)) :=
    ofNat_primitive.comp (Primrec.nat_div.comp
      (Primrec.nat_add.comp hc (Primrec.const 1)) (Primrec.const 2))
  have hindex : Primrec (fun p : P => p.2.2.2.2.1-(((p.2.2.2.1+1)/2 : Nat) : Int)) := by
    apply (add_primitive.comp hj (negate_primitive.comp hhalf)).of_eq
    intro p
    simp only [sub_eq_add_neg]
  have hS := Primrec.list_cons.comp (shiftLetter_primitive.comp ha) (Primrec.const [])
  have hcontext := FiniteRangeExposure.Proof.contextTail_primitive.comp
    (hA.pair (hS.pair ((Primrec.const 0).pair (hm.pair (hc.pair hj)))))
  have hretained := retainedWord_primitive.comp
    (hA.pair ((Primrec.const 0).pair (hm.pair hc)))
  have hguard := QuadraticWordGuardCompletion.Proof.guardTail_primitive.comp
    (hretained.pair (hB.pair (hindex.pair (hk.pair (ha.pair hb)))))
  exact Primrec.nat_max.comp hcontext hguard

theorem guardPrograms : Targets.GuardPrograms :=
  ⟨retainedWord_primitive,kernelGuardTail_primitive,quadraticGuardTail_primitive⟩

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
