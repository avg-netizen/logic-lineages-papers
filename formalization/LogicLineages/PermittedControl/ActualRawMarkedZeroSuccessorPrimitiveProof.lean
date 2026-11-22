module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorPlanPrimitiveProof
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorMovePrimitiveProof
import LogicLineages.PermittedControl.ActualRawSignedCleanupPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison.LayeredComparison
open MixedSameRankResidue ActualRawSignedCleanup ActualRawSignedStaticCeiling

private theorem shiftAddPrimitive : Primrec₂ shiftAddCode := by
  let A := Option Int × Option Int
  let P := A × Int
  let Q := P × Int
  have next : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have first : Primrec (fun p : Q => p.1.2) := Primrec.snd.comp Primrec.fst
  have second : Primrec (Prod.snd : Q → Int) := Primrec.snd
  have total := IntegerAlgorithms.Proof.add_primitive.comp first second
  have inside := Primrec.option_map next total.to₂
  have outside := Primrec.option_bind (Primrec.fst : Primrec (Prod.fst : A → Option Int)) inside.to₂
  apply outside.to₂.of_eq
  intro a b
  cases a <;> cases b <;> rfl

private theorem shiftsPrimitive : Primrec shiftsCode := by
  let A := List MarkCode × (MarkCode × Option Int)
  have head : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have tail : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have step := shiftAddPrimitive.comp (shiftOnePrimitive.comp head) tail
  exact Primrec.list_foldr Primrec.id (Primrec.const (some (0 : Int))) step.to₂

private theorem cohortPrimitive : Primrec cohortCode :=
  Primrec.listFilterMap Primrec.id (markedPrefixPrimitive.comp Primrec.snd).to₂

private theorem outsidePrimitive : Primrec outsideCode := by
  let A := List MarkCode × MarkCode
  have coeff : Primrec (fun p : MarkCode => p.1.1) := Primrec.fst.comp Primrec.fst
  have bit : Primrec (Prod.snd : MarkCode → Bool) := Primrec.snd
  have keep : Primrec (fun m : MarkCode => decide (m.1.1 ≠ 0) && !m.2) :=
    Primrec.and.comp ((Primrec.eq.comp coeff (Primrec.const (0 : Int))).not.decide)
      (Primrec.not.comp bit)
  have filtered : Primrec (fun ms : List MarkCode =>
      ms.filter (fun m => decide (m.1.1 ≠ 0) && !m.2)) := by
    apply (Primrec.listFilter (Primrec.eq.comp keep (Primrec.const true))).of_eq
    intro ms
    apply List.filter_congr
    intro m _
    change decide ((decide (m.1.1 ≠ 0) && !m.2) = true) =
      (decide (m.1.1 ≠ 0) && !m.2)
    generalize (decide (m.1.1 ≠ 0) && !m.2) = bitValue
    cases bitValue <;> rfl
  have get : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  exact Primrec.list_map filtered get.to₂

theorem exactRawMarkedSuccessorEffectivity : ExactRawMarkedSuccessorEffectivity := by
  let A := Int × List MarkCode
  let P := A × Int
  have ms : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have K : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have shift : Primrec (Prod.snd : P → Int) := Primrec.snd
  have cost := IntegerAlgorithms.Proof.add_primitive.comp K shift
  have ps := cohortPrimitive.comp ms
  have moved := movedPrimitive.comp (leastPrimitive.comp ps) ps
  have before := Primrec.list_append.comp (outsidePrimitive.comp ms) moved
  have cleaned := exactRawInitialCleanupEffectivity.2.2.2.comp (cost.pair before)
  have step := (Primrec.option_some.comp cleaned).to₂
  exact Primrec.option_bind (shiftsPrimitive.comp (Primrec.snd : Primrec (Prod.snd : A → List MarkCode))) step

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
