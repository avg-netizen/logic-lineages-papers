module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroReplayTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodePrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodePrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
open ActualRawCanonicalNode (GroupedArgs groupedCode groupedPrimitive)
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualCanonicalOperandGrouping (RawTerm groupRaw)
open ActualCanonicalOperandGroupingCode (groupRawPrimitive)

private def stepArgs (p : RawSyntax × AnswerCode) : GroupedArgs :=
  (p.1.1,groupRaw p.1.2,p.2)

private theorem stepArgsPrimitive : Primrec stepArgs := by
  let A := RawSyntax × AnswerCode
  have c : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have tape : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  exact c.pair ((groupRawPrimitive.comp tape).pair Primrec.snd)

private theorem stepLiteral (p : RawSyntax × AnswerCode) :
    (groupedCode (stepArgs p)).2 = stepCode p := rfl

theorem stepPrimitive : Primrec stepCode :=
  (Primrec.snd.comp (groupedPrimitive.comp stepArgsPrimitive)).of_eq stepLiteral

private abbrev AdvanceArgs := Option RawSyntax × AnswerCode

private def advanceArgs (p : AdvanceArgs × RawSyntax) : RawSyntax × AnswerCode :=
  (p.2,p.1.2)

private theorem advanceArgsPrimitive : Primrec advanceArgs :=
  Primrec.snd.pair (Primrec.snd.comp Primrec.fst)

private theorem advanceLiteral (p : AdvanceArgs) :
    p.1.bind (fun st => stepCode (advanceArgs (p,st))) = advanceCode p.1 p.2 := rfl

theorem advancePrimitive : Primrec₂ advanceCode := by
  have next := stepPrimitive.comp advanceArgsPrimitive
  exact ((Primrec.option_bind Primrec.fst next.to₂).of_eq advanceLiteral).to₂

private theorem foldPrimitive {A X S : Type} [Primcodable A] [Primcodable X] [Primcodable S]
    {xs : A → List X} {init : A → S} {step : S → X → S}
    (items : Primrec xs) (hinit : Primrec init) (next : Primrec₂ step) :
    Primrec (fun p => (xs p).foldl step (init p)) :=
  Primrec.list_foldl items hinit (next.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
    (Primrec.snd.comp₂ Primrec₂.right))

theorem replayPrimitive : Primrec replayCode := by
  let A := SequenceCode × RawSyntax
  have answers : Primrec (Prod.fst : A → SequenceCode) := Primrec.fst
  have init : Primrec (fun p : A => some p.2) := Primrec.option_some.comp Primrec.snd
  exact (foldPrimitive answers init advancePrimitive).of_eq (fun _ => rfl)

theorem exactRawCanonicalZeroReplayEffectivity : ExactRawCanonicalZeroReplayEffectivity :=
  ⟨stepPrimitive,advancePrimitive,replayPrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
