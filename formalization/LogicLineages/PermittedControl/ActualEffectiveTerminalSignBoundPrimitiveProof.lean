module
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodePrimitiveProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open ActualMixedRowLeadingSum ActualZeroClassCommonTail
open ActualZeroEdgeAlphabetCode ActualSyntaxChargeBudget
open SelectedCountOnlyClass (omegaSquareNote)

private theorem normPrimitive : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

private theorem finiteMaxPrimitive {α β : Type} [Primcodable α] [Primcodable β]
    {items : α → List β} {cost : α → β → Nat}
    (sequence : Primrec items) (one : Primrec₂ cost) :
    Primrec (fun a => finiteMax (cost a) (items a)) := by
  let A := α × (β × Nat)
  have context : Primrec (fun p : A => p.1) := Primrec.fst
  have item : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have last : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr sequence (Primrec.const 0)
    (Primrec.nat_max.comp (one.comp context item) last).to₂

private theorem prefixChoicesPrimitive : Primrec prefixChoicesCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have rank : Primrec (fun op : LowerOperandCode => op.2.1) := Primrec.fst.comp Primrec.snd
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have lam := Primrec.fst.comp endpoints
  have mu := Primrec.snd.comp endpoints
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  have choice : Primrec prefixChoiceCode :=
    Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
      (Primrec.option_some.comp (rank.pair (lam.pair eta))) (Primrec.const none)
  exact Primrec.listFilterMap Primrec.id (choice.comp Primrec.snd).to₂

private theorem correctionPrimitive : Primrec correctionBoundCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have field : Primrec (fun op : LowerOperandCode => op.2.2) := Primrec.snd.comp Primrec.snd
  have endpoints := Primrec.snd.comp (Primrec.snd.comp field)
  have mu := Primrec.snd.comp endpoints
  have norm := normPrimitive.comp mu
  have ceil := ofNat_primitive.comp (Primrec.nat_div.comp (Primrec.succ.comp norm) (Primrec.const 2))
  have eq : Primrec (fun op : LowerOperandCode =>
      (1 : Int) - (((rawNormCode op.2.2.2.2.2 + 1) / 2 : Nat) : Int)) := by
    simpa only [sub_eq_add_neg] using
      add_primitive.comp (Primrec.const (1 : Int)) (negate_primitive.comp ceil)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (abs_primitive.comp eq) (Primrec.const 0)

private theorem shortPrimitive : Primrec shortLengthCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have slot : Primrec (fun op : LowerOperandCode => shortGapLengthCode op.2.2.2.2.1 op.2.2.2.2.2) :=
    shortFieldPreprocessingEffective.2.1.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) slot (Primrec.const 0)

private theorem correctionMaxPrimitive : Primrec correctionMaxCode :=
  finiteMaxPrimitive Primrec.id (correctionPrimitive.comp Primrec.snd).to₂

private theorem prefixShortMaxPrimitive : Primrec prefixShortMaxCode := by
  let A := AlphabetCode × PrefixCode
  have slot : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact finiteMaxPrimitive prefixChoicesPrimitive
    (shortFieldPreprocessingEffective.2.1.comp (Primrec.fst.comp slot) (Primrec.snd.comp slot)).to₂

private theorem cleanupMaxPrimitive : Primrec cleanupMaxCode :=
  finiteMaxPrimitive ActualZeroEdgeAlphabetCode.codeEffectivity.1 (shortPrimitive.comp Primrec.snd).to₂

private theorem edgeFactorPrimitive : Primrec edgeFactorCode :=
  Primrec.nat_add.comp (Primrec.nat_add.comp correctionMaxPrimitive prefixShortMaxPrimitive)
    (Primrec.nat_mul.comp (Primrec.const 3) cleanupMaxPrimitive)

private theorem syntaxMassPrimitive : Primrec syntaxMassCode := by
  let A := List WeightedCode × (WeightedCode × Nat)
  have weight : Primrec (fun p : A => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have last : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (abs_primitive.comp weight) last).to₂

private theorem powThreePrimitive : Primrec (fun n : Nat => (3 : Nat) ^ n) := by
  let step := fun (_ : Nat) (last : Nat) => last * 3
  have update : Primrec₂ step :=
    (Primrec.nat_mul.comp (Primrec.snd : Primrec (Prod.snd : Nat × Nat → Nat))
      (Primrec.const 3)).to₂
  apply (Primrec.nat_rec₁ (1 : Nat) update).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec 1 step n * 3 = 3 ^ (n+1)
      rw [ih,Nat.pow_succ]

private theorem suppliedPrimitive :
    Primrec (fun p : Nat × Int × List WeightedCode => signCeilingAtBudgetCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Int × List WeightedCode
  have depth : Primrec (fun p : A => p.1) := Primrec.fst
  have c : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have keys : Primrec (fun p : A => p.2.2.map Prod.snd) :=
    Primrec.list_map terms (Primrec.snd.comp Primrec.snd).to₂
  have alphabet := ActualZeroEdgeAlphabetCode.codeEffectivity.2.2.comp depth keys
  have mass := Primrec.nat_mul.comp (powThreePrimitive.comp depth) (syntaxMassPrimitive.comp terms)
  have step := Primrec.nat_mul.comp mass (edgeFactorPrimitive.comp alphabet)
  have absolute := Primrec.nat_add.comp (abs_primitive.comp c) (Primrec.nat_mul.comp depth step)
  have offset := Primrec.nat_add.comp absolute (Primrec.nat_mul.comp mass (correctionMaxPrimitive.comp alphabet))
  have slope := Primrec.nat_mul.comp (Primrec.const 2) mass
  exact Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec.nat_add.comp (Primrec.nat_add.comp slope offset) (Primrec.const 2))

theorem codeEffectivity : CodeEffectivity := by
  let A := Nat × Int × List WeightedCode
  have c : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact ⟨suppliedPrimitive, suppliedPrimitive.comp ((budgetCodeExact.1.comp Primrec.fst terms).pair
    (c.pair terms))⟩

end LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
