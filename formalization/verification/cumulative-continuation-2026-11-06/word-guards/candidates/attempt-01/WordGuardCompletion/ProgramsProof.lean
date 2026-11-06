module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
open PolynomialGraphCompletion

theorem letterOffset_primitive : Primrec letterOffset :=
  LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem letterTail_primitive : Primrec letterTail :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd)) letterOffset_primitive)
    (Primrec.const 4)

theorem wordOffset_primitive : Primrec wordOffset := by
  have hs : Primrec (fun p : Letter × Nat => letterOffset p.1+p.2) :=
    Primrec.nat_add.comp (letterOffset_primitive.comp Primrec.fst) Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) (hs.comp Primrec.snd).to₂

theorem wordTail_primitive : Primrec wordTail := by
  have hs : Primrec (fun p : Letter × Nat => letterTail p.1+letterOffset p.1+p.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (letterTail_primitive.comp Primrec.fst)
        (letterOffset_primitive.comp Primrec.fst)) Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) (hs.comp Primrec.snd).to₂

theorem reachTail_primitive : Primrec (fun p : Word × Nat => reachTail p.1 p.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp (wordTail_primitive.comp Primrec.fst)
      (wordOffset_primitive.comp Primrec.fst)) Primrec.snd

theorem tailPrograms : Targets.TailPrograms :=
  ⟨letterTail_primitive,letterOffset_primitive,wordTail_primitive,
    wordOffset_primitive,reachTail_primitive⟩

end LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
