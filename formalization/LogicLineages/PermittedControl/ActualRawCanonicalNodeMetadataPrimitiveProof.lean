module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingLabelPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
open PreparedProjection (LowerOperandCode)
open ActualCanonicalOperandGrouping (RawTerm)
open ActualRawComparisonCeiling (labelPrimitive)

theorem activeLabelPrimitive : Primrec activeLabelCode := by
  have w : Primrec (Prod.fst : RawTerm → Int) := Primrec.fst
  have row : Primrec (Prod.snd : RawTerm → LowerOperandCode) := Primrec.snd
  exact Primrec.ite (Primrec.eq.comp w (Primrec.const 0)) (Primrec.const none) (labelPrimitive.comp row)

theorem labelsPrimitive : Primrec labelsCode :=
  Primrec.listFilterMap Primrec.id ((activeLabelPrimitive.comp Primrec.snd).to₂)

private theorem nonlinearPrimitive : Primrec nonlinearCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have field : Primrec (fun op : LowerOperandCode => op.2.2) := Primrec.snd.comp Primrec.snd
  have kind : Primrec (fun op : LowerOperandCode => op.2.2.1) := Primrec.fst.comp field
  have exp : Primrec (fun op : LowerOperandCode => op.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp field)
  have positive := (Primrec.nat_lt.comp (Primrec.const 0) exp).decide
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp kind (Primrec.const 0)) positive (Primrec.const true))
    (Primrec.eq.comp tag (Primrec.const 2)).decide

theorem highestPrimitive : Primrec₂ highestCode := by
  let A := Nat × RawTerm
  have w : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have op : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have rank : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp op)
  have onTop := (Primrec.eq.comp rank Primrec.fst)
  have nonzero := (Primrec.eq.comp w (Primrec.const 0)).not
  have code : Primrec (fun p : A => highestCode p.1 p.2) :=
    Primrec.and.comp (nonzero.and onTop).decide (nonlinearPrimitive.comp op)
  exact code.to₂

private theorem anyPrimitive {A X : Type} [Primcodable A] [Primcodable X]
    {xs : A → List X} {test : A → X → Bool} (items : Primrec xs) (check : Primrec₂ test) :
    Primrec (fun p => (xs p).any (test p)) := by
  let S := A × (X × Bool)
  have a : Primrec (Prod.fst : S → A) := Primrec.fst
  have x : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have rest : Primrec (fun s : S => s.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun s : S => test s.1 s.2.1 || s.2.2) :=
    Primrec.or.comp (check.comp a x) rest
  apply (Primrec.list_foldr items (Primrec.const false) step.to₂).of_eq
  intro p
  induction xs p with
  | nil => rfl
  | cons h t ih => simp only [List.foldr_cons,List.any_cons,ih]

theorem tapeHighestPrimitive : Primrec₂ tapeHighestCode := by
  let A := Nat × List RawTerm
  have items : Primrec (Prod.snd : A → List RawTerm) := Primrec.snd
  have test : Primrec₂ (fun (p : A) t => highestCode p.1 t) :=
    highestPrimitive.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have h : Primrec (fun p : A => tapeHighestCode p.1 p.2) := anyPrimitive items test
  exact h.to₂

private theorem notLessPrimitive : Primrec notLessCode :=
  (Primrec.eq.comp Primrec.id (Primrec.const 0)).not.decide

private theorem allNotLessPrimitive : Primrec (fun xs : List Nat => xs.all notLessCode) := by
  let S := List Nat × (Nat × Bool)
  have x : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have t : Primrec (fun s : S => s.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun s : S => notLessCode s.2.1 && s.2.2) :=
    Primrec.and.comp (notLessPrimitive.comp x) t
  apply (Primrec.list_foldr Primrec.id (Primrec.const true) step.to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons h t ih =>
    change t.foldr (fun b s => notLessCode b && s) true = t.all notLessCode at ih
    change (notLessCode h && t.foldr (fun b s => notLessCode b && s) true) =
      (notLessCode h && t.all notLessCode)
    rw [ih]

theorem flagsPrimitive :
    Primrec (fun p : Nat × Nat × List Nat => flagsCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List Nat
  let S := A × Nat
  have width : Primrec (fun s : S => s.1.1) := Primrec.fst.comp Primrec.fst
  have j : Primrec (Prod.snd : S → Nat) := Primrec.snd
  have answers : Primrec (fun s : S => s.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have dropped := Primrec.list_drop.comp (Primrec.nat_mul.comp j width) answers
  have block := Primrec.list_take.comp width dropped
  have flag : Primrec (fun s : S => ((s.1.2.2.drop (s.2*s.1.1)).take s.1.1).all notLessCode) :=
    allNotLessPrimitive.comp block
  have indices : Primrec (fun p : A => List.range p.2.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_map indices flag.to₂

theorem classFlagsPrimitive : Primrec₂ classFlagsCode := by
  let A := List RawTerm × List Nat
  have width : Primrec (fun p : A => (labelsCode p.1).length) :=
    Primrec.list_length.comp (labelsPrimitive.comp Primrec.fst)
  have code : Primrec (fun p : A => classFlagsCode p.1 p.2) :=
    flagsPrimitive.comp (width.pair (width.pair Primrec.snd))
  exact code.to₂

theorem exactRawCanonicalNodeEffectivity : ExactRawCanonicalNodeEffectivity :=
  ⟨activeLabelPrimitive,labelsPrimitive,highestPrimitive,tapeHighestPrimitive,flagsPrimitive,classFlagsPrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
