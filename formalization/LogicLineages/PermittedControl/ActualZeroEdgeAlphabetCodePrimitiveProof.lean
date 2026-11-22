module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeTargets
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
open OrdinalComparison PreparedProjection ConcreteCountPairReplacement
open SelectedCountOnlyClass (omegaSquareNote)

private theorem prefixChoicePrimitive : Primrec prefixChoiceCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have rank : Primrec (fun op : LowerOperandCode => op.2.1) := Primrec.fst.comp Primrec.snd
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have lam := Primrec.fst.comp endpoints
  have mu := Primrec.snd.comp endpoints
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (Primrec.option_some.comp (rank.pair (lam.pair eta))) (Primrec.const none)

private theorem prefixKeyPrimitive : Primrec prefixKeyCode :=
  (Primrec.const 2).pair (Primrec.fst.pair
    ((Primrec.const 1).pair ((Primrec.const 0).pair Primrec.snd)))

private theorem pairKeyPrimitive : Primrec₂ pairKeyCode := by
  let A := PrefixCode × PrefixCode
  have rank : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have lo : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have delta := ordinalSubCodeEffective.comp (Primrec.fst.comp hi) (Primrec.snd.comp hi)
  have endpoint := ordinalAddCodeEffective.comp (Primrec.snd.comp lo) delta
  exact ((Primrec.const 2).pair (rank.pair
    ((Primrec.const 1).pair ((Primrec.const 0).pair ((Primrec.fst.comp lo).pair endpoint))))).to₂

private theorem pairChoicePrimitive : Primrec₂ pairChoiceCode := by
  let A := PrefixCode × PrefixCode
  have lo : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have key : Primrec (fun p : A => pairKeyCode p.1 p.2) := pairKeyPrimitive
  exact (Primrec.ite (Primrec.nat_lt.comp lo hi)
    (Primrec.option_some.comp key) (Primrec.const none)).to₂

private theorem prefixChoicesPrimitive : Primrec prefixChoicesCode :=
  Primrec.listFilterMap Primrec.id (prefixChoicePrimitive.comp Primrec.snd).to₂

private theorem pairChoicesPrimitive : Primrec pairChoicesCode := by
  let A := (List PrefixCode × PrefixCode) × PrefixCode
  have lo : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun p : A => p.2) := Primrec.snd
  have choose : Primrec (fun p : A => pairChoiceCode p.1.2 p.2) := pairChoicePrimitive.comp lo hi
  have row : Primrec (fun p : List PrefixCode × PrefixCode => p.1.filterMap (pairChoiceCode p.2)) :=
    Primrec.listFilterMap Primrec.fst choose.to₂
  exact Primrec.list_flatMap Primrec.id row.to₂

private theorem expandPrimitive : Primrec expandCode := by
  have keys : Primrec (fun alphabet : AlphabetCode => (prefixChoicesCode alphabet).map prefixKeyCode) :=
    Primrec.list_map prefixChoicesPrimitive (prefixKeyPrimitive.comp Primrec.snd).to₂
  have pairs := pairChoicesPrimitive.comp prefixChoicesPrimitive
  exact Primrec.list_append.comp Primrec.id (Primrec.list_append.comp keys pairs)

private theorem stepsPrimitive : Primrec₂ expandStepsCode := by
  have step : Primrec₂ (fun (_ : AlphabetCode) (z : Nat × AlphabetCode) => expandCode z.2) :=
    (expandPrimitive.comp (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (Primrec.id : Primrec (id : AlphabetCode → AlphabetCode)) step).swap

private theorem collectPrimitive : Primrec₂ collectCode := by
  let A := (Nat × AlphabetCode) × Nat
  have cols : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have depth : Primrec (fun p : A => p.2) := Primrec.snd
  have each := stepsPrimitive.comp depth cols
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) each.to₂).to₂

theorem codeEffectivity : CodeEffectivity := ⟨expandPrimitive,stepsPrimitive,collectPrimitive⟩

end LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
