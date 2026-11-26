module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
public import LogicLineages.StandardControlCurrent.PolicyPartialMergePrograms
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPrograms

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum
open PolicyShape (State)
open CurrentGroundAnnotationCode

theorem chooseProgram {α β : Type} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) :=
  (Computable.cond hp.decide.to_comp hf hg).of_eq (fun a => by simp)

theorem markerNode (tag : Nat) : Primrec (fun p : Nat × Nat => 4*Nat.pair p.1 p.2+tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair) (Primrec.const tag)

private theorem payloadStep : Primrec (fun x : (List Nat × List Nat) × Bool => markStep (some x.1) x.2) := by
  let A := (List Nat × List Nat) × Bool
  have hx : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hz : Primrec (fun p : A => (p.1.1.getD 0 0)) := (Primrec.list_getD 0).comp hx (Primrec.const 0)
  have hr : Primrec (fun p : A => (p.1.2.getD 0 0)) := (Primrec.list_getD 0).comp hs (Primrec.const 0)
  have hl : Primrec (fun p : A => (p.1.2.getD 1 0)) := (Primrec.list_getD 0).comp hs (Primrec.const 1)
  have hn : Primrec (fun p : A => 4*Nat.pair (p.1.2.getD 1 0) (p.1.2.getD 0 0)+2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hl hr)) (Primrec.const 2)
  have hleaf := Primrec.option_some.comp ((Primrec.list_tail.comp hx).pair (Primrec.list_cons.comp hz hs))
  have hjoin := Primrec.option_some.comp (hx.pair (Primrec.list_cons.comp hn
    (Primrec.list_tail.comp (Primrec.list_tail.comp hs))))
  have hf := Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hx) (Primrec.const 0))
    (Primrec.const (none : State)) hleaf
  have ht := Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp hs) (Primrec.const 2))
    (Primrec.const (none : State)) hjoin
  apply (Primrec.cond (Primrec.snd : Primrec (fun p : A => p.2)) ht hf).of_eq
  rintro ⟨⟨xs,stack⟩,b⟩
  cases b <;> cases xs <;> cases stack with
  | nil => rfl
  | cons y ys => cases ys <;> rfl

theorem stepProgram : Primrec (fun x : State × Bool => markStep x.1 x.2) := by
  have hsome : Primrec₂ (fun x : State × Bool => fun s : List Nat × List Nat => markStep (some s) x.2) :=
    (payloadStep.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  apply (Primrec.option_casesOn Primrec.fst (Primrec.const none) hsome).of_eq
  rintro ⟨s,b⟩
  cases s <;> rfl

theorem runProgram : Primrec (fun x : List Bool × State => CurrentGroundAnnotationCode.run x.1 x.2) :=
  Primrec.list_foldl Primrec.fst Primrec.snd (stepProgram.comp Primrec.snd).to₂


private theorem markerExpand : Primrec (fun x : List Bool × List Nat =>
    PolicyShape.finish (run x.1 (some (x.2,[])))) :=
  PolicyShapeProgramsProof.finishProgram.comp
    (runProgram.comp (Primrec.fst.pair
      (Primrec.option_some.comp (Primrec.snd.pair (Primrec.const [])))))

attribute [local irreducible] CurrentGroundAnnotationCode.run
  CurrentGroundAnnotationCode.macroCode PolicyShape.selector

theorem markerProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × List Nat => macroCode p x.1 x.2.1 x.2.2) := by
  have hs : Computable (fun x : Nat × Nat × List Nat => PolicyShape.selector p x.1 x.2.1) :=
    Computable.comp (f := fun y : Nat × Nat => PolicyShape.selector p y.1 y.2)
      (g := fun x : Nat × Nat × List Nat => (x.1,x.2.1)) hp
      (Computable.fst.pair (Computable.fst.comp Computable.snd))
  unfold CurrentGroundAnnotationCode.macroCode
  exact Computable.comp
    (f := fun y : List Bool × List Nat => PolicyShape.finish (run y.1 (some (y.2,[]))))
    (g := fun x : Nat × Nat × List Nat => (PolicyShape.selector p x.1 x.2.1,x.2.2))
    markerExpand.to_comp (hs.pair (Computable.snd.comp Computable.snd))

theorem repeated (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat => repeatCode p x.1 x.2) := by
  have hc : Primrec (fun x : Nat × Nat => x.1-1) :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
  have hrep : Primrec (fun x : Nat × Nat => List.replicate x.1 x.2) := by
    apply (Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (fun x : Nat × Nat => x.1)))
      (Primrec.snd.comp Primrec.fst).to₂).of_eq
    intro x
    simp
  unfold CurrentGroundAnnotationCode.repeatCode
  exact chooseProgram (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Computable.const (some 0))
    ((markerProgram p hp).comp ((Computable.const (PolicyShape.siteCode .scalarRepeat)).pair
      (hc.pair hrep).to_comp))

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPrograms
