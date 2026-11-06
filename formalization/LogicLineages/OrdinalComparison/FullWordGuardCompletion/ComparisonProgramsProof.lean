module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonDefinitions
public import Mathlib.Computability.Primrec.List
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProgramsProof
open LayeredComparison.IntegerAlgorithms.Proof

theorem int_lt_primitive : PrimrecRel (fun a b : Int => a < b) := by
  have hd : Primrec (fun p : Int × Int => p.1 + -p.2) :=
    add_primitive.comp Primrec.fst (negate_primitive.comp Primrec.snd)
  have hs : PrimrecPred (fun p : Int × Int => Int.sign (p.1 + -p.2) = -1) :=
    Primrec.eq.comp (sign_primitive.comp hd) (Primrec.const (-1 : Int))
  exact hs.of_eq (fun p => by rw [Int.sign_eq_neg_one_iff_neg]; omega)

theorem orderNat_primitive : Primrec₂ orderNat :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd)
      (Primrec.const 1) (Primrec.const 2))

theorem orderInt_primitive : Primrec₂ orderInt :=
  Primrec.ite int_lt_primitive (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd)
      (Primrec.const 1) (Primrec.const 2))

theorem liftTie_primitive : Primrec₂ liftTie :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
    Primrec.fst Primrec.snd

theorem reverseOrder_primitive : Primrec reverseOrder :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0) (Primrec.const 1))

theorem lexOrder_primitive : Primrec₂ lexOrder :=
  liftTie_primitive.comp Primrec.snd Primrec.fst

theorem signFormula_primitive :
    Primrec (fun p : Nat × Nat => signFormula p.1 p.2) := by
  have hr : PrimrecRel (fun sign (p : Nat × Nat) => liftTie p.1 sign = p.2) :=
    Primrec.eq.comp
      (liftTie_primitive.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  exact hr.listFilter.comp (Primrec.const [0,1,2]) Primrec.id

theorem makeGuards_primitive : Primrec makeGuards :=
  (signFormula_primitive.comp (Primrec.id.pair (Primrec.const 0))).pair
    ((signFormula_primitive.comp (Primrec.id.pair (Primrec.const 1))).pair
      (signFormula_primitive.comp (Primrec.id.pair (Primrec.const 2))))

theorem guardAt_primitive : Primrec (fun p : Guards × Nat => guardAt p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.fst.comp Primrec.fst)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProgramsProof
