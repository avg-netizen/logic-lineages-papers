module
public import LogicLineages.PermittedControl.GroundComparisonPositiveTargets
import LogicLineages.OrdinalComparison.RawComparisonProof
import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
import Mathlib.Computability.Primrec.List

public section
namespace LogicLineages.PermittedControl.GroundComparisonPositive
open OrdinalComparison Source Source.ForwardTranslation

private theorem getD_map {α β : Type*} (g : α → β) (d : α) :
    ∀ (l : List α) (j : Nat), (l.map g).getD j (g d) = g (l.getD j d)
  | [], j => by simp
  | x :: l, 0 => by simp
  | x :: l, j+1 => by simp [getD_map g d l j]

private theorem foldr_all (P : Nat → Bool) :
    ∀ l : List Nat, l.foldr (fun j acc => P j && acc) true = true ↔ ∀ j ∈ l, P j = true
  | [] => by simp
  | x :: l => by simp [foldr_all P l]

/-- The note at position `j`, zero beyond the list. -/
private noncomputable def noteAt (zs : List ClosedPositive) (j : Nat) : NONote :=
  (zs.map ClosedPositive.evaluate).getD j 0

private theorem codeAt (zs : List ClosedPositive) (j : Nat) :
    ((zs.map closedPositiveCode).map encodedClosedPositive).getD j zeroNoteCode =
      rawNoteEncode (noteAt zs j).1 := by
  have h : (zs.map closedPositiveCode).map encodedClosedPositive =
      (zs.map ClosedPositive.evaluate).map (fun n : NONote => rawNoteEncode n.1) := by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left (fun z _ => encodedClosedPositiveCorrect z)
  rw [h]
  exact getD_map (fun n : NONote => rawNoteEncode n.1) 0 (zs.map ClosedPositive.evaluate) j

private theorem paddedAt (zs : List ClosedPositive) (j : Nat) :
    paddedValue zs j = (noteAt zs j).1.repr := by
  have h : zs.map (fun z => z.evaluate.1.repr) =
      (zs.map ClosedPositive.evaluate).map (fun n : NONote => n.1.repr) := by
    rw [List.map_map]
    rfl
  unfold paddedValue
  rw [h]
  exact getD_map (fun n : NONote => n.1.repr) 0 (zs.map ClosedPositive.evaluate) j

private theorem coordAt (equal : Bool) (a b : NONote) :
    coordTest equal (rawNoteEncode a.1) (rawNoteEncode b.1) = true ↔
      (if equal = true then a.1.repr = b.1.repr else a.1.repr ≤ b.1.repr) := by
  have hc := rawComparisonOrdinalCorrect a b
  unfold coordTest
  cases equal with
  | true =>
    simp only [if_true,decide_eq_true_eq]
    exact hc.2.1
  | false =>
    simp only [Bool.false_eq_true,if_false,decide_eq_true_eq]
    rw [ne_eq,hc.2.2,not_lt]

private theorem noteAt_beyond (zs : List ClosedPositive) (j : Nat) (h : zs.length ≤ j) :
    noteAt zs j = 0 := by
  unfold noteAt
  exact List.getD_eq_default _ _ (by simpa using h)

theorem exactPositiveTest : ExactPositiveTest := by
  intro equal as bs
  unfold positiveTest
  simp only [codeAt,List.length_map]
  rw [foldr_all]
  constructor
  · intro h j
    rw [paddedAt,paddedAt]
    by_cases hj : j < max as.length bs.length
    · exact (coordAt equal _ _).1 (h j (List.mem_range.2 hj))
    · have ha : noteAt as j = 0 := noteAt_beyond as j (by omega)
      have hb : noteAt bs j = 0 := noteAt_beyond bs j (by omega)
      rw [ha,hb]
      cases equal <;> simp
  · intro h j _
    apply (coordAt equal _ _).2
    have hj := h j
    rw [paddedAt,paddedAt] at hj
    exact hj

theorem positiveTestEffectivity : PositiveTestEffectivity := by
  let X := Bool × List Nat × List Nat
  have eqTag : Primrec (fun x : X => x.1) := Primrec.fst
  have la : Primrec (fun x : X => x.2.1) := Primrec.fst.comp Primrec.snd
  have lb : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have n : Primrec (fun x : X => max x.2.1.length x.2.2.length) :=
    Primrec.nat_max.comp (Primrec.list_length.comp la) (Primrec.list_length.comp lb)
  have idx : Primrec (fun x : X => List.range (max x.2.1.length x.2.2.length)) := Primrec.list_range.comp n
  have enc : Primrec encodedClosedPositive := encodedClosedPositivePrimitiveRecursive
  have ma : Primrec (fun x : X => x.2.1.map encodedClosedPositive) :=
    Primrec.list_map la (enc.comp Primrec.snd).to₂
  have mb : Primrec (fun x : X => x.2.2.map encodedClosedPositive) :=
    Primrec.list_map lb (enc.comp Primrec.snd).to₂
  let Y := X × (Nat × Bool)
  have j : Primrec (fun y : Y => y.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun y : Y => y.2.2) := Primrec.snd.comp Primrec.snd
  have ga : Primrec (fun y : Y => (y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode) :=
    (Primrec.list_getD zeroNoteCode).comp (ma.comp Primrec.fst) j
  have gb : Primrec (fun y : Y => (y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode) :=
    (Primrec.list_getD zeroNoteCode).comp (mb.comp Primrec.fst) j
  have cmp : Primrec (fun y : Y => rawComparisonCode
      ((y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode)
      ((y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode)) := by
    have h := rawComparisonPrimitiveRecursive.comp ga gb
    exact h
  have tagT : PrimrecPred (fun y : Y => y.1.1 = true) :=
    Primrec.eq.comp (eqTag.comp Primrec.fst) (Primrec.const true)
  have isEq : Primrec (fun y : Y => decide (rawComparisonCode
      ((y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode)
      ((y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode) = 1)) :=
    (Primrec.eq.comp cmp (Primrec.const 1)).decide
  have isLe : Primrec (fun y : Y => decide (rawComparisonCode
      ((y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode)
      ((y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode) ≠ 2)) :=
    (Primrec.eq.comp cmp (Primrec.const 2)).not.decide
  have coord : Primrec (fun y : Y => coordTest y.1.1
      ((y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode)
      ((y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode)) := by
    have h := Primrec.ite tagT isEq isLe
    exact h.of_eq (fun y => rfl)
  have step : Primrec (fun y : Y => coordTest y.1.1
      ((y.1.2.1.map encodedClosedPositive).getD y.2.1 zeroNoteCode)
      ((y.1.2.2.map encodedClosedPositive).getD y.2.1 zeroNoteCode) && y.2.2) :=
    Primrec.and.comp coord acc
  have h := Primrec.list_foldr idx (Primrec.const true) step.to₂
  exact h.of_eq (fun x => rfl)

theorem fullGroundComparisonPositive : FullGroundComparisonPositive :=
  ⟨exactPositiveTest,positiveTestEffectivity⟩

#print axioms fullGroundComparisonPositive
end LogicLineages.PermittedControl.GroundComparisonPositive
