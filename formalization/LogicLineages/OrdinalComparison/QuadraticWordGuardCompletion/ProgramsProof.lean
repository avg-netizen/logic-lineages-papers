module
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem scalarTail_primitive : Primrec (fun p : Int × Int × Nat => scalarTail p.1 p.2.1 p.2.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst)
        (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)) (Primrec.const 8)

theorem guardTail_primitive : Primrec
    (fun p : Word × Word × Int × Int × Int × Int =>
      guardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let P := Word × Word × Int × Int × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hj := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hk := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have ha := Primrec.fst.comp hr4
  have hb := Primrec.snd.comp hr4
  have hK := Primrec.nat_add.comp
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp ha)
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp hb)
  have hT := scalarTail_primitive.comp (hj.pair (hk.pair hK))
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hA.pair hT))
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hB.pair hT))

theorem guardPrograms : Targets.GuardPrograms := ⟨scalarTail_primitive,guardTail_primitive⟩

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
