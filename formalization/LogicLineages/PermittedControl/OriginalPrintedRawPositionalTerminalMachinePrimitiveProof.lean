module
public import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalTapePrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal

private abbrev Input := Nat × State

private theorem localPrimitive : Primrec localStep := by
  have tag : Primrec (Prod.fst : Input → Nat) := Primrec.fst
  have stk : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have bits : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd : Primrec (fun p : Input => p.2.1.getD 0 false) :=
    (Primrec.list_getD false).comp stk (Primrec.const 0)
  have hd1 : Primrec (fun p : Input => p.2.1.getD 1 false) :=
    (Primrec.list_getD false).comp stk (Primrec.const 1)
  have nextBit : Primrec (fun p : Input => p.2.2.getD 0 false) :=
    (Primrec.list_getD false).comp bits (Primrec.const 0)
  have stTail : Primrec (fun p : Input => p.2.1.tail) := Primrec.list_tail.comp stk
  have stDrop : Primrec (fun p : Input => p.2.1.tail.tail) :=
    Primrec.list_tail.comp stTail
  have bitTail : Primrec (fun p : Input => p.2.2.tail) := Primrec.list_tail.comp bits
  have pushTrue : Primrec (fun p : Input => some (true :: p.2.1,p.2.2)) :=
    Primrec.option_some.comp ((Primrec.list_cons.comp (Primrec.const true) stk).pair bits)
  have pushFalse : Primrec (fun p : Input => some (false :: p.2.1,p.2.2)) :=
    Primrec.option_some.comp ((Primrec.list_cons.comp (Primrec.const false) stk).pair bits)
  have pushBit : Primrec (fun p : Input =>
      if 0 < p.2.2.length then some (p.2.2.getD 0 false :: p.2.1,p.2.2.tail) else none) :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp bits))
      (Primrec.option_some.comp ((Primrec.list_cons.comp nextBit stk).pair bitTail)) (Primrec.const none)
  have neg : Primrec (fun p : Input =>
      if 0 < p.2.1.length then some ((!p.2.1.getD 0 false) :: p.2.1.tail,p.2.2) else none) :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp stk))
      (Primrec.option_some.comp ((Primrec.list_cons.comp (Primrec.not.comp hd) stTail).pair bits))
      (Primrec.const none)
  have binary (b : Bool → Bool → Bool) (hb : Primrec₂ b) : Primrec (fun p : Input =>
      if 2 ≤ p.2.1.length then some (b (p.2.1.getD 1 false) (p.2.1.getD 0 false) :: p.2.1.tail.tail,p.2.2)
        else none) :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp stk))
      (Primrec.option_some.comp ((Primrec.list_cons.comp (hb.comp hd1 hd) stDrop).pair bits))
      (Primrec.const none)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) pushTrue
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) pushFalse
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) pushBit
        (Primrec.ite (Primrec.eq.comp tag (Primrec.const 3)) neg
          (Primrec.ite (Primrec.eq.comp tag (Primrec.const 4)) (binary Bool.and Primrec.and)
            (Primrec.ite (Primrec.eq.comp tag (Primrec.const 5)) (binary Bool.or Primrec.or)
              (Primrec.const none))))))

private theorem stepPrimitive : Primrec₂ step := by
  let A := Option State × Nat
  have inner : Primrec₂ (fun (p : A) (st : State) => localStep (p.2,st)) :=
    (localPrimitive.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd) :
      Primrec (fun p : A × State => localStep (p.1.2,p.2))).to₂
  have h : Primrec (fun p : A => step p.1 p.2) := Primrec.option_bind Primrec.fst inner
  exact h.to₂

private theorem runPrimitive : Primrec (fun p : Tape × Option State => run p.1 p.2) := by
  let A := Tape × Option State
  have hs : Primrec₂ (fun (_ : A) (q : Option State × Nat) => step q.1 q.2) :=
    (stepPrimitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd) :
      Primrec (fun p : A × (Option State × Nat) => step p.2.1 p.2.2)).to₂
  exact Primrec.list_foldl Primrec.fst Primrec.snd hs

private theorem extractPrimitive : Primrec extract := by
  have n : Primrec (fun s : State => s.1.length) := Primrec.list_length.comp Primrec.fst
  have hd : Primrec (fun s : State => s.1.getD 0 false) :=
    (Primrec.list_getD false).comp Primrec.fst (Primrec.const 0)
  exact Primrec.ite (Primrec.eq.comp n (Primrec.const 1))
    (Primrec.option_some.comp (hd.pair Primrec.snd)) (Primrec.const none)

private theorem completePrimitive : Primrec complete := by
  have n : Primrec (fun p : Bool × List Bool => p.2.length) := Primrec.list_length.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp n (Primrec.const 0))
    (Primrec.option_some.comp Primrec.fst) (Primrec.const none)

private theorem readPrimitive : Primrec readCode := by
  have t : Primrec (fun p : Args => tape p.1) := tapePrimitive.comp Primrec.fst
  have init : Primrec (fun p : Args => some (([] : Stack),p.2)) :=
    Primrec.option_some.comp ((Primrec.const []).pair Primrec.snd)
  exact Primrec.option_bind (runPrimitive.comp (t.pair init))
    (extractPrimitive.comp Primrec.snd).to₂

private theorem finishPrimitive : Primrec finishCode :=
  Primrec.option_bind readPrimitive (completePrimitive.comp Primrec.snd).to₂

theorem exactOriginalRawPositionalEffectivity : ExactOriginalRawPositionalEffectivity :=
  ⟨tapePrimitive,readPrimitive,finishPrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
