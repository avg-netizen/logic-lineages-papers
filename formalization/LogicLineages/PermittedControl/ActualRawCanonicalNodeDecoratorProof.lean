module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeDecoratorTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof
import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassDomainProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm exactCanonicalTape)
open ActualRawCanonicalNodeMetadata (activeLabelCode labelCalibrationOne labelsCalibration classFlagsCalibration)
open ActualZeroSuccessorMarkedClass (Marked decorate exactDecorationDomain)
open ActualFullValueLabels (activeLabel)

private def walk : List RawTerm → List Bool → Option (List RawMarked)
  | [], [] => some []
  | [], _::_ => none
  | t::ts, mask =>
      match activeLabelCode t,mask with
      | none,_ => (walk ts mask).map (List.cons (t,false))
      | some _,[] => none
      | some _,b::rest => (walk ts rest).map (List.cons (t,b))

private theorem foldNone (ts : List RawTerm) :
    ts.foldl paintStep none = none := by
  induction ts with
  | nil => rfl
  | cons t rest ih => exact ih

private theorem appendReversed (mark : RawMarked) (rev : List RawMarked)
    (ms : Option (List RawMarked)) :
    ms.map (fun out => (mark :: rev).reverse ++ out) =
      (ms.map (List.cons mark)).map (fun out => rev.reverse ++ out) := by
  cases ms with
  | none => rfl
  | some out =>
    simp only [Option.map_some,List.reverse_cons,List.append_assoc,List.singleton_append]

private theorem foldWalk (ts : List RawTerm) (bits : List Bool) (rev : List RawMarked) :
    paintFinish (ts.foldl paintStep (some (bits,rev))) =
      (walk ts bits).map (fun out => rev.reverse ++ out) := by
  induction ts generalizing bits rev with
  | nil => cases bits <;> simp [paintFinish,walk]
  | cons t ts ih =>
    rw [List.foldl_cons]
    cases h : activeLabelCode t with
    | none =>
      have step : paintStep (some (bits,rev)) t = some (bits,(t,false)::rev) := by
        simp [paintStep,h]
      have head : walk (t::ts) bits = (walk ts bits).map (List.cons (t,false)) := by
        cases bits <;> simp [walk,h]
      rw [step,ih,head]
      exact appendReversed (t,false) rev _
    | some label =>
      cases bits with
      | nil =>
        have step : paintStep (some ([],rev)) t = none := by simp [paintStep,h]
        have head : walk (t::ts) [] = none := by simp [walk,h]
        rw [step,foldNone,head] <;> rfl
      | cons b more =>
        have step : paintStep (some (b::more,rev)) t = some (more,(t,b)::rev) := by
          simp [paintStep,h]
        have head : walk (t::ts) (b::more) = (walk ts more).map (List.cons (t,b)) := by
          simp [walk,h]
        rw [step,ih,head]
        exact appendReversed (t,b) rev _

private theorem codeWalk (ts : List RawTerm) (bits : List Bool) :
    decorateCode ts bits = walk ts bits := by
  unfold decorateCode
  rw [foldWalk]
  cases walk ts bits <;> rfl

private theorem encodedCons (head : Marked) (rest : Option (List Marked)) :
    (rest.map (List.map encodeMark)).map (List.cons (encodeMark head)) =
      (rest.map (List.cons head)).map (List.map encodeMark) := by
  cases rest <;> rfl

private theorem walkCalibration (ts : List WeightedOperand) (mask : List Bool) :
    walk (ts.map encodeTerm) mask = (decorate ts mask).map (List.map encodeMark) := by
  induction ts generalizing mask with
  | nil => cases mask <;> rfl
  | cons t ts ih =>
    rw [List.map_cons]
    cases h : activeLabel t with
    | none =>
      have rawLabel : activeLabelCode (encodeTerm t) = none := by
        simp [labelCalibrationOne,h]
      have rawHead : walk (encodeTerm t :: ts.map encodeTerm) mask =
          (walk (ts.map encodeTerm) mask).map (List.cons (encodeTerm t,false)) := by
        cases mask <;> simp [walk,rawLabel]
      have typedHead : decorate (t::ts) mask = (decorate ts mask).map (List.cons (t,false)) := by
        cases mask <;> simp [decorate,h]
      rw [rawHead,typedHead,ih]
      exact encodedCons (t,false) _
    | some label =>
      have rawLabel : activeLabelCode (encodeTerm t) =
          some (ActualRawComparisonCeiling.encodeLabel label) := by simp [labelCalibrationOne,h]
      cases mask with
      | nil =>
        have rawHead : walk (encodeTerm t :: ts.map encodeTerm) [] = none := by
          simp [walk,rawLabel]
        have typedHead : decorate (t::ts) [] = none := by simp [decorate,h]
        rw [rawHead,typedHead] <;> rfl
      | cons b more =>
        have rawHead : walk (encodeTerm t :: ts.map encodeTerm) (b::more) =
            (walk (ts.map encodeTerm) more).map (List.cons (encodeTerm t,b)) := by
          simp [walk,rawLabel]
        have typedHead : decorate (t::ts) (b::more) =
            (decorate ts more).map (List.cons (t,b)) := by simp [decorate,h]
        rw [rawHead,typedHead,ih]
        exact encodedCons (t,b) _

theorem exactRawDecorateCalibration : ExactRawDecorateCalibration := by
  intro ts bits
  rw [codeWalk,walkCalibration]

theorem exactLiteralRawDecorationDomain : ExactLiteralRawDecorationDomain := by
  intro ts bits
  have domain := exactDecorationDomain ts bits
  refine ⟨?_,?_⟩
  · rw [exactRawDecorateCalibration,Option.isSome_map,labelsCalibration,List.length_map]
    exact domain.1
  · intro ms measured
    rw [exactRawDecorateCalibration] at measured
    cases h : decorate ts bits with
    | none => simp [h] at measured
    | some out =>
      simp only [h,Option.map_some,Option.some.injEq] at measured
      subst ms
      have tape := domain.2 out h
      simpa only [List.map_map,Function.comp_def,encodeMark] using congrArg (List.map encodeTerm) tape

theorem exactCanonicalSuppliedDecoration : ExactCanonicalSuppliedDecoration := by
  intro ts answers
  simp only
  rw [← exactCanonicalTape.1 ts,classFlagsCalibration,exactRawDecorateCalibration]

end LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
