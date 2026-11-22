module
public import LogicLineages.PermittedControl.ActualBitFamilyRawClosedTargets
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawClosed
open ActualBitFamilyRawLayout (RawBitRow RawFamily)
open HeterogeneousSignedMatrixSlice (TestCode RawRow)
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (abs_primitive sign_primitive)

private theorem admittedPrimitive : Primrec admittedCode := by
  have tag : Primrec (Prod.fst : TestCode → Nat) := Primrec.fst
  have mod : Primrec (Prod.snd : TestCode → Nat) := Primrec.snd
  exact Primrec.or.comp
    (Primrec.and.comp ((Primrec.nat_lt.comp tag (Primrec.const 3)).decide)
      ((Primrec.eq.comp mod (Primrec.const 0)).decide))
    (Primrec.and.comp ((Primrec.eq.comp tag (Primrec.const 3)).decide)
      ((Primrec.nat_lt.comp (Primrec.const 0) mod).decide))

private theorem testPrimitive : Primrec testCode := by
  let A := TestCode × Int
  have val : Primrec (Prod.snd : A → Int) := Primrec.snd
  have tag : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have mod : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have sign := sign_primitive.comp val
  have eqz := (Primrec.eq.comp val (Primrec.const (0 : Int))).decide
  have sgz := (Primrec.eq.comp sign (Primrec.const (0 : Int))).decide
  have sgo := (Primrec.eq.comp sign (Primrec.const (1 : Int))).decide
  have rem := (Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp val) mod)
    (Primrec.const 0)).decide
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) eqz
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) (Primrec.or.comp sgz sgo)
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) sgo rem))

private theorem rowPrimitive : Primrec rowCode := by
  have row : Primrec (Prod.fst : RawBitRow → RawRow) := Primrec.fst
  have test : Primrec (fun r : RawBitRow => r.1.1) := Primrec.fst.comp row
  have constant : Primrec (fun r : RawBitRow => r.1.2.1) := Primrec.fst.comp (Primrec.snd.comp row)
  have operands : Primrec (fun r : RawBitRow => r.1.2.2) := Primrec.snd.comp (Primrec.snd.comp row)
  have blank := (Primrec.eq.comp (Primrec.list_length.comp operands) (Primrec.const 0)).decide
  have wanted := (Primrec.eq.comp (testPrimitive.comp (test.pair constant)) Primrec.snd).decide
  exact Primrec.and.comp (admittedPrimitive.comp test) (Primrec.and.comp blank wanted)

private theorem listTestPrimitive {A : Type} [Primcodable A] {p : A → Bool}
    (hp : Primrec p) (zero : Bool) (combine : Bool → Bool → Bool)
    (hc : Primrec₂ combine) :
    Primrec (fun xs : List A => xs.foldr (fun item acc => combine (p item) acc) zero) := by
  have step : Primrec (fun q : A × Bool => combine (p q.1) q.2) :=
    hc.comp (hp.comp Primrec.fst) Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const zero) (step.comp Primrec.snd).to₂

private theorem clausePrimitive : Primrec clauseCode := by
  apply (listTestPrimitive rowPrimitive true Bool.and Primrec.and).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (rowCode x && xs.foldr (fun item acc => rowCode item && acc) true) = (rowCode x && clauseCode xs)
    exact congrArg (fun b => rowCode x && b) ih

private theorem familyPrimitive : Primrec closedCode := by
  apply (listTestPrimitive clausePrimitive false Bool.or Primrec.or).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (clauseCode x || xs.foldr (fun item acc => clauseCode item || acc) false) = (clauseCode x || closedCode xs)
    exact congrArg (fun b => clauseCode x || b) ih

theorem exactClosedRawEffectivity : ExactClosedRawEffectivity :=
  ⟨admittedPrimitive,testPrimitive,rowPrimitive,clausePrimitive,familyPrimitive⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawClosed
