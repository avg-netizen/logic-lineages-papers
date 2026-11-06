module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem predecessorHead_primitive : Primrec predecessorHead := by
  have hj : Primrec (fun a : Letter => a.2.2.2 - 1) := by
    simpa only [sub_eq_add_neg] using
      (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const (-1 : Int)) : Primrec (fun a : Letter => a.2.2.2 + (-1)))
  exact Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair hj))

theorem factorTail_primitive : Primrec factorTail :=
  Primrec.nat_max.comp WordGuardCompletion.Proof.letterTail_primitive
    (WordGuardCompletion.Proof.letterTail_primitive.comp predecessorHead_primitive)

theorem wordFactorTail_primitive : Primrec
    (fun p : Word × Letter => wordFactorTail p.1 p.2) :=
  WordGuardCompletion.Proof.reachTail_primitive.comp
    (Primrec.fst.pair (factorTail_primitive.comp Primrec.snd))

theorem contextTail_primitive : Primrec
    (fun p : Word × Letter × Word => contextTail p.1 p.2.1 p.2.2) := by
  let P := Word × Letter × Word
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hS : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hcontext : Primrec (fun p : P => p.1 ++ [p.2.1] ++ p.2.2) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp hA (Primrec.list_cons.comp ha (Primrec.const []))) hS
  exact Primrec.nat_max.comp
    (wordFactorTail_primitive.comp (hA.pair ha))
    (WordGuardCompletion.Proof.wordTail_primitive.comp hcontext)

theorem cancellationTail_primitive : Primrec
    (fun p : Word × Word × Letter => cancellationTail p.1 p.2.1 p.2.2) :=
  Primrec.nat_max.comp
    (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.fst)
    (wordFactorTail_primitive.comp Primrec.snd)

theorem factorPrograms : Targets.FactorPrograms :=
  ⟨predecessorHead_primitive, factorTail_primitive, wordFactorTail_primitive,
    contextTail_primitive, cancellationTail_primitive⟩

end LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
