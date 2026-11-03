module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Dedup
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Program

/-! Elementary data programs for the unchanged finite-box constructor. The
positive-word recursion is reproduced narrowly rather than importing the
single-core formula compiler and its larger proof closure. -/

theorem words_primitive : Primrec₂ singleCoreBoxWords := by
  let A := Nat × (Nat × List (List Nat))
  have hPrev : Primrec (fun p : A × Nat => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hMap : Primrec₂ (fun p : A => fun value : Nat =>
      p.2.2.map (fun word => (value+1)::word)) :=
    Primrec.list_map hPrev (Primrec.list_cons.comp
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hRange : Primrec (fun p : A => List.range (p.1-1)) :=
    Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  have hStep : Primrec₂ (fun bound : Nat => fun state : Nat × List (List Nat) =>
      (List.range (bound-1)).flatMap
        (fun value => state.2.map (fun word => (value+1)::word))) :=
    Primrec.list_flatMap hRange hMap
  apply (Primrec.nat_rec (Primrec.const ([[]] : List (List Nat))) hStep).of_eq
  intro bound n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (List.range (bound-1)).flatMap (fun value =>
      (Nat.rec (motive := fun _ => List (List Nat)) [[]]
        (fun _ previous => (List.range (bound-1)).flatMap
          (fun value => previous.map (fun word => (value+1)::word))) n).map
            (fun word => (value+1)::word)) = _
    rw [ih]
    rfl

theorem dedup_primitive : Primrec (fun xs : List Nat => xs.dedup) := by
  have hm : PrimrecPred (fun p : Nat × List Nat => p.1 ∈ p.2) :=
    (Primrec.nat_lt.comp Primrec.list_idxOf
      (Primrec.list_length.comp Primrec.snd)).of_eq
        (fun _ => List.idxOf_lt_length_iff)
  have hs : Primrec₂ (fun (_ : List Nat) => fun p : Nat × List Nat =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2) :=
    (Primrec.ite (hm.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const ([] : List Nat)) hs).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [id_eq, List.foldr_cons] at ih ⊢
    rw [ih, List.dedup_cons']

theorem pointCode_primitive : Primrec₂ pointCode := by
  let D := (List Nat × List Nat) × Nat
  have hsupport : Primrec (fun p : D => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hword : Primrec (fun p : D => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hleft : Primrec (fun p : D => 4 * p.1.1.getD p.2 0 + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        ((Primrec.list_getD (0 : Nat)).comp hsupport Primrec.snd))
      (Primrec.const 1)
  have hright : Primrec (fun p : D => 4 * p.1.2.getD p.2 1) :=
    Primrec.nat_mul.comp (Primrec.const 4)
      ((Primrec.list_getD (1 : Nat)).comp hword Primrec.snd)
  have hpoint : Primrec (fun p : D =>
      [(2, 4 * p.1.1.getD p.2 0 + 1, 4 * p.1.2.getD p.2 1)]) :=
    Primrec.list_cons.comp ((Primrec.const 2).pair (hleft.pair hright))
      (Primrec.const [])
  exact CommonHeadCode.Program.conjoin_primitive.comp
    (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) hpoint.to₂)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Program
