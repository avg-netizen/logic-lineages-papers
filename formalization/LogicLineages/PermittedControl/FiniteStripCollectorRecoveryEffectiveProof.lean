module
public import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryTargets
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldEffectiveProof
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripCollectorRecovery
open OrdinalComparison PreparedProjection FieldComparison

private theorem shapePrimitive : Primrec operandShape := by
  have ht : Primrec (fun c : LowerOperandCode => c.1) := Primrec.fst
  have hf : Primrec (fun c : LowerOperandCode => c.2.2) := Primrec.snd.comp Primrec.snd
  have hk := Primrec.fst.comp hf
  have ha := Primrec.fst.comp (Primrec.snd.comp hf)
  have hl := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have hm := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have hz := (Primrec.eq.comp hf (Primrec.const (0,0,0,0))).decide
  have ho := (((Primrec.eq.comp hk (Primrec.const 0)).and
    ((Primrec.eq.comp hl (Primrec.const 0)).and (Primrec.eq.comp hm (Primrec.const 0)))).or
    (Primrec.eq.comp hk (Primrec.const 1))).decide
  have hc := ((Primrec.eq.comp ht (Primrec.const 2)).and
    ((Primrec.eq.comp hk (Primrec.const 1)).and (Primrec.eq.comp ha (Primrec.const 0)))).decide
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) hz
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) ho hc)

private theorem computedIf {A B : Type} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : PrimrecPred p)
    (u v : A → B) (hu : Computable u) (hv : Computable v) :
    Computable (fun a => if p a then u a else v a) := by
  exact (Computable.cond hp.decide.to_comp hu hv).of_eq (fun a => by simp)

private theorem fieldComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fieldRead f) := by
  let A := Nat × LowerOperandCode
  have ha : Computable (fun p : A => p.1) := Computable.fst
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hfield : Computable (fun p : A => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hl : Computable (fun p : A => p.2.2.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hfield))
  have hm : Computable (fun p : A => p.2.2.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hfield))
  have hcoord := Computable.option_some.comp (Computable.option_some.comp ha)
  have hvalue := (closedOrdinaryFieldEffective f hf).2.1.comp hfield ha
  have hcount := (closedOrdinaryFieldEffective f hf).2.2.comp (hl.pair (hm.pair ha))
  exact computedIf (fun p : A => p.2.1 = 0)
    (Primrec.eq.comp ht (Primrec.const 0)) _ _ hcoord
    (computedIf (fun p : A => p.2.1 = 1)
      (Primrec.eq.comp ht (Primrec.const 1)) _ _ hvalue hcount)

private def tagOne (name : Nat) (v : Option Nat) : Option (List (Nat × Nat)) :=
  v.map (fun b => [(name,b)])
private def tagRead (name : Nat) (v : ClosedNaturalFieldResult) : ReadResult :=
  v.map (tagOne name)

private theorem tagOnePrimitive : Primrec₂ tagOne := by
  have hs : Primrec (fun p : (Nat × Option Nat) × Nat => [(p.1.1,p.2)]) :=
    Primrec.list_cons.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd) (Primrec.const [])
  exact Primrec.option_map Primrec.snd hs.to₂

private theorem tagReadPrimitive : Primrec₂ tagRead :=
  Primrec.option_map Primrec.snd
    (tagOnePrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem readComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fun p : Nat × Nat => readCode f p.1 p.2) := by
  let A := (Nat × Nat) × NamedCode
  have hn : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hr : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp hc)
  have hx : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbad : PrimrecPred (fun p : A => p.2.1 = 0 ∨ operandShape p.2.2 = false) :=
    (Primrec.eq.comp hn (Primrec.const 0)).or
      (Primrec.eq.comp (shapePrimitive.comp hc) (Primrec.const false))
  have hskip : PrimrecPred (fun p : A => p.2.2.2.1 ≠ p.1.1) :=
    (Primrec.eq.comp hr hx).not
  have hmatched := tagReadPrimitive.to_comp.comp hn.to_comp
    ((fieldComputable f hf).comp ha.to_comp hc.to_comp)
  exact computedIf _ hbad _ _ (Computable.const none)
    (computedIf _ hskip _ _ (Computable.const (some (some []))) hmatched)

private def prependOne (hs : List (Nat × Nat)) (ts : Option (List (Nat × Nat))) :=
  ts.map (hs ++ ·)
private def prependRead (hs : List (Nat × Nat)) (ts : ReadResult) : ReadResult :=
  ts.map (prependOne hs)
private def appendPresent (tail : ReadResult) (hs : Option (List (Nat × Nat))) : ReadResult :=
  hs.elim (some none) (fun xs => prependRead xs tail)

private theorem prependOnePrimitive : Primrec₂ prependOne :=
  Primrec.option_map Primrec.snd
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
private theorem prependReadPrimitive : Primrec₂ prependRead :=
  Primrec.option_map Primrec.snd
    (prependOnePrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
private theorem appendPresentPrimitive : Primrec₂ appendPresent := by
  apply (Primrec.option_casesOn Primrec.snd (Primrec.const (some none))
    (prependReadPrimitive.comp₂ Primrec₂.right (Primrec.fst.comp₂ Primrec₂.left))).of_eq
  rintro ⟨tail,hs⟩
  cases hs <;> rfl

private theorem appendPrimitive : Primrec₂ appendResult := by
  apply (Primrec.option_casesOn Primrec.fst (Primrec.const none)
    (appendPresentPrimitive.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
  intro p
  rcases p with ⟨head,tail⟩
  cases head with
  | none => rfl
  | some hs => cases hs <;> rfl

private theorem collectComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fun p : Nat × Nat => collectCode f p.1 p.2) := by
  let A := (Nat × Nat) × List NamedCode
  have hs : Computable₂ (fun p : A => fun q : NamedCode × ReadResult =>
      appendResult (readCode f p.1.1 p.1.2 q.1) q.2) :=
    appendPrimitive.to_comp.comp
      ((readComputable f hf).comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  exact ComparisonAssembly.computable_foldr (default : NamedCode)
    Computable.snd (Computable.const (some (some []))) hs

theorem collectorEffective : CollectorEffective := by
  intro f hf
  exact ⟨readComputable f hf,collectComputable f hf⟩
end LogicLineages.PermittedControl.FiniteStripCollectorRecovery
