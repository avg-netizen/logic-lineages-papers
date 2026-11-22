module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLayout
open HeterogeneousSignedMatrixSlice (RawRow)
open OriginalMatrixLowDimensionCode (rawSupport)
open MixedSameRankResidue (WeightedCode)

theorem occurrencesPrimitive : Primrec occurrences := by
  have rawRows : Primrec (fun c : List RawBitRow => c.map Prod.fst) :=
    Primrec.list_map Primrec.id
      ((Primrec.fst : Primrec (Prod.fst : RawBitRow → RawRow)).comp Primrec.snd).to₂
  have allRows : Primrec (fun family : RawFamily => family.flatMap (List.map Prod.fst)) :=
    Primrec.list_flatMap Primrec.id (rawRows.comp Primrec.snd).to₂
  have rank : Primrec (fun t : WeightedCode => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have atoms : Primrec (fun r : RawRow => r.2.2.map (fun t => t.2.2.1)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) (rank.comp Primrec.snd).to₂
  have allAtoms : Primrec rawSupport :=
    Primrec.list_flatMap Primrec.id (atoms.comp Primrec.snd).to₂
  exact allAtoms.comp allRows

private theorem appearsPrimitive : Primrec₂ appears := by
  let A := List Nat × Nat
  let Q := A × (Nat × Bool)
  have name : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have key : Primrec (fun p : Q => p.1.2) := Primrec.snd.comp Primrec.fst
  have seen : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Q => decide (p.2.1 = p.1.2) || p.2.2) :=
    Primrec.or.comp ((Primrec.eq.comp name key).decide) seen
  have h : Primrec (fun p : A => appears p.1 p.2) :=
    Primrec.list_foldr Primrec.fst (Primrec.const false) step.to₂
  exact h.to₂

theorem namesPrimitive : Primrec names := by
  let A := List Nat × (Nat × Nat)
  have atom : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have rest : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have largest : Primrec (fun ns : List Nat => ns.foldr max 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0) (Primrec.nat_max.comp atom rest).to₂
  have indices : Primrec (fun ns : List Nat => List.range ((ns.foldr max 0)+1)) :=
    Primrec.list_range.comp (Primrec.succ.comp largest)
  have h : Primrec (fun p : List Nat × Nat =>
      if appears p.1 p.2 then some p.2 else none) := by
    apply (Primrec.cond (appearsPrimitive.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).of_eq
    intro p
    cases appears p.1 p.2 <;> rfl
  have layout : Primrec namesFrom := Primrec.listFilterMap indices h.to₂
  exact layout.comp occurrencesPrimitive

theorem exactRawLayoutEffectivity : ExactRawLayoutEffectivity :=
  ⟨occurrencesPrimitive,namesPrimitive⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawLayout
