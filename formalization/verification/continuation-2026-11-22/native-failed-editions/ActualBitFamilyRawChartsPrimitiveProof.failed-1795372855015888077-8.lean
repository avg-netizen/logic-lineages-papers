module
public import LogicLineages.PermittedControl.ActualBitFamilyRawChartsTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawCharts
open ActualBitFamilyRawLayout (namesPrimitive)
open ActualFiniteOrderBranches (Entry Pattern choices onto patterns)

private theorem allPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {xs : A → List B} {pred : A → B → Bool} (hl : Primrec xs) (hp : Primrec₂ pred) :
    Primrec fun a => (xs a).all (pred a) := by
  let Q := A × (B × Bool)
  have root : Primrec (fun p : Q => p.1) := Primrec.fst
  have item : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Q => pred p.1 p.2.1 && p.2.2) :=
    Primrec.and.comp (hp.comp root item) acc
  apply (Primrec.list_foldr hl (Primrec.const true) step.to₂).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.all_cons,ih]

private theorem filterPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {xs : A → List B} {pred : A → B → Bool} (hl : Primrec xs) (hp : Primrec₂ pred) :
    Primrec fun a => (xs a).filter (pred a) := by
  have keep : Primrec (fun p : A × B => if pred p.1 p.2 then some p.2 else none) := by
    apply (Primrec.cond (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).of_eq
    intro p
    cases pred p.1 p.2 <;> rfl
  apply (Primrec.listFilterMap hl keep.to₂).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons x xs ih =>
      cases h : pred a x <;> simp [List.filterMap_cons,List.filter_cons,h,ih]

theorem choicesPrimitive : Primrec (fun p : Nat × List Nat => choices p.1 p.2) := by
  let X := Nat × List Nat
  let T := X × (Nat × List (List Entry))
  let Q := T × Nat
  let R := Q × List Entry
  have k : Primrec (fun p : T => p.1.1) := Primrec.fst.comp Primrec.fst
  have digits : Primrec (fun p : T => List.range p.1.1) := Primrec.list_range.comp k
  have tail : Primrec (fun p : Q => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have name : Primrec (fun p : R => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have rank : Primrec (fun p : R => p.1.2) := Primrec.snd.comp Primrec.fst
  have prepend : Primrec (fun p : R => (p.1.1.2.1,p.1.2) :: p.2) :=
    Primrec.list_cons.comp (name.pair rank) Primrec.snd
  have mapRows : Primrec (fun p : Q => p.1.2.2.map (List.cons (p.1.2.1,p.2))) :=
    Primrec.list_map tail prepend.to₂
  have step : Primrec (fun p : T =>
      (List.range p.1.1).flatMap (fun j => p.2.2.map (List.cons (p.2.1,j)))) :=
    Primrec.list_flatMap digits mapRows.to₂
  apply (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : X → List Nat))
    (Primrec.const ([[]] : List (List Entry))) step.to₂).of_eq
  rintro ⟨width,source⟩
  induction source with
  | nil => rfl
  | cons head tail ih => simp only [List.foldr_cons,choices,ih]

private theorem containsPrimitive : Primrec (fun p : List Nat × Nat => p.1.contains p.2) := by
  have index : Primrec (fun p : List Nat × Nat => p.1.idxOf p.2) :=
    Primrec.list_idxOf.comp Primrec.fst Primrec.snd
  have length : Primrec (fun p : List Nat × Nat => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  apply (Primrec.nat_lt.comp index length).decide.of_eq
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.idxOf_lt_length_iff,List.contains_iff_mem]

theorem ontoPrimitive : Primrec (fun p : Nat × List Entry => onto p.1 p.2) := by
  let X := Nat × List Entry
  let Q := X × Nat
  have digits : Primrec (fun p : X => List.range p.1) := Primrec.list_range.comp Primrec.fst
  have entries : Primrec (fun p : Q => p.1.2) := Primrec.snd.comp Primrec.fst
  have rankList : Primrec (fun p : Q => p.1.2.map Prod.snd) :=
    Primrec.list_map entries (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : Q × Entry → Entry))).to₂
  have used : Primrec (fun p : Q => (p.1.2.map Prod.snd).contains p.2) :=
    containsPrimitive.comp (rankList.pair Primrec.snd)
  exact allPrimitive digits used.to₂

theorem patternsPrimitive : Primrec patterns := by
  let Q := List Nat × Nat
  let R := Q × List Entry
  have widths : Primrec (fun ns : List Nat => List.range (ns.length+1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length)
  have possible : Primrec (fun p : Q => choices p.2 p.1) :=
    choicesPrimitive.comp (Primrec.snd.pair Primrec.fst)
  have width : Primrec (fun p : R => p.1.2) := Primrec.snd.comp Primrec.fst
  have viable : Primrec (fun p : R => onto p.1.2 p.2) :=
    ontoPrimitive.comp (width.pair Primrec.snd)
  have good : Primrec (fun p : Q => (choices p.2 p.1).filter (onto p.2)) :=
    filterPrimitive possible viable.to₂
  have pack : Primrec (fun p : R => (p.1.2,p.2)) := width.pair Primrec.snd
  have chart : Primrec (fun p : Q =>
      ((choices p.2 p.1).filter (onto p.2)).map (fun es => (p.2,es))) :=
    Primrec.list_map good pack.to₂
  exact Primrec.list_flatMap widths chart.to₂

theorem nonemptyPatternsPrimitive : Primrec nonemptyPatterns := by
  have pos : PrimrecPred (fun p : Pattern => 0 < p.1) :=
    Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst
  exact (Primrec.listFilter pos).comp patternsPrimitive

theorem exactRawChartEffectivity : ExactRawChartEffectivity :=
  ⟨choicesPrimitive,ontoPrimitive,patternsPrimitive,nonemptyPatternsPrimitive,
    nonemptyPatternsPrimitive.comp namesPrimitive⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawCharts
