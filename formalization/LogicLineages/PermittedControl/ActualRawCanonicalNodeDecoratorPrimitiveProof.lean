module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeDecoratorTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
open ActualCanonicalOperandGrouping (RawTerm)
open ActualRawCanonicalNodeMetadata (activeLabelCode activeLabelPrimitive)

private theorem payloadPrimitive {X : Type} [Primcodable X] {active : X → Bool}
    (hactive : Primrec active) :
    Primrec (fun p : X × (List Bool × List (X × Bool)) =>
      if active p.1 then
        p.2.1.head?.map (fun b => (p.2.1.tail,(p.1,b)::p.2.2))
      else some (p.2.1,(p.1,false)::p.2.2)) := by
  let P := X × (List Bool × List (X × Bool))
  let Q := P × Bool
  have obj : Primrec (Prod.fst : P → X) := Primrec.fst
  have bits : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have rev : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have item : Primrec (fun q : Q => q.1.1) := obj.comp Primrec.fst
  have bit : Primrec (Prod.snd : Q → Bool) := Primrec.snd
  have rest : Primrec (fun q : Q => q.1.2.1.tail) :=
    Primrec.list_tail.comp (bits.comp Primrec.fst)
  have withBit : Primrec (fun q : Q => (q.1.2.1.tail,(q.1.1,q.2)::q.1.2.2)) :=
    rest.pair (Primrec.list_cons.comp (item.pair bit) (rev.comp Primrec.fst))
  have enabled : Primrec (fun p : P =>
      p.2.1.head?.map (fun b => (p.2.1.tail,(p.1,b)::p.2.2))) :=
    Primrec.option_map (Primrec.list_head?.comp bits) withBit.to₂
  have disabled : Primrec (fun p : P => some (p.2.1,(p.1,false)::p.2.2)) :=
    Primrec.option_some.comp (bits.pair (Primrec.list_cons.comp (obj.pair (Primrec.const false)) rev))
  apply (Primrec.cond (hactive.comp obj) enabled disabled).of_eq
  intro p
  cases active p.1 <;> rfl

private def rawActive (t : RawTerm) : Bool := (activeLabelCode t).isSome

private theorem rawActivePrimitive : Primrec rawActive :=
  Primrec.option_isSome.comp activeLabelPrimitive

private def statePayload (p : RawTerm × State) : Option State :=
  if rawActive p.1 then
    p.2.1.head?.map (fun b => (p.2.1.tail,(p.1,b)::p.2.2))
  else some (p.2.1,(p.1,false)::p.2.2)

private theorem payloadLiteral (p : RawTerm × State) :
    (if rawActive p.1 then
      p.2.1.head?.map (fun b => (p.2.1.tail,(p.1,b)::p.2.2))
    else some (p.2.1,(p.1,false)::p.2.2)) = statePayload p := rfl

private theorem statePayloadPrimitive : Primrec statePayload :=
  (payloadPrimitive rawActivePrimitive).of_eq payloadLiteral

private def payloadArgs (p : (Option State × RawTerm) × State) : RawTerm × State :=
  (p.1.2,p.2)

private theorem payloadArgsPrimitive : Primrec payloadArgs :=
  (Primrec.snd.comp Primrec.fst).pair Primrec.snd

private theorem paintStepLiteral (p : Option State × RawTerm) :
    p.1.bind (fun s => statePayload (payloadArgs (p,s))) = paintStep p.1 p.2 := rfl

theorem paintStepPrimitive : Primrec₂ paintStep := by
  have run := statePayloadPrimitive.comp payloadArgsPrimitive
  have step : Primrec (fun p : Option State × RawTerm =>
      p.1.bind (fun s => statePayload (payloadArgs (p,s)))) :=
    Primrec.option_bind Primrec.fst run.to₂
  exact (step.of_eq paintStepLiteral).to₂

private theorem finishOnStatePrimitive : Primrec (fun p : State =>
    if p.1.length = 0 then some p.2.reverse else none) := by
  have length : Primrec (fun p : State => p.1.length) := Primrec.list_length.comp Primrec.fst
  have reverse : Primrec (fun p : State => p.2.reverse) := Primrec.list_reverse.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp length (Primrec.const 0))
    (Primrec.option_some.comp reverse) (Primrec.const none)

theorem paintFinishPrimitive : Primrec paintFinish :=
  Primrec.option_bind Primrec.id (finishOnStatePrimitive.comp Primrec.snd).to₂

private theorem foldPrimitive {A X S : Type} [Primcodable A] [Primcodable X] [Primcodable S]
    {tape : A → List X} {seed : A → S} {step : S → X → S}
    (ht : Primrec tape) (hs : Primrec seed) (hp : Primrec₂ step) :
    Primrec (fun p => (tape p).foldl step (seed p)) :=
  Primrec.list_foldl ht hs (hp.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
    (Primrec.snd.comp₂ Primrec₂.right))

theorem decoratePrimitive : Primrec₂ decorateCode := by
  let A := List RawTerm × List Bool
  have tape : Primrec (Prod.fst : A → List RawTerm) := Primrec.fst
  have seed : Primrec (fun p : A => some (p.2,([] : List RawMarked))) :=
    Primrec.option_some.comp (Primrec.snd.pair (Primrec.const []))
  have walk := foldPrimitive tape seed paintStepPrimitive
  have whole : Primrec (fun p : A => decorateCode p.1 p.2) :=
    paintFinishPrimitive.comp walk
  exact whole.to₂

theorem exactRawDecorateEffectivity : ExactRawDecorateEffectivity :=
  ⟨paintStepPrimitive,paintFinishPrimitive,decoratePrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
