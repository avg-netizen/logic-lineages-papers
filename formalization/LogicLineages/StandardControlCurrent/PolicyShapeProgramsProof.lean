module
public import LogicLineages.StandardControlCurrent.PolicyShapeTargets
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyShape

private theorem payloadStep : Primrec (fun x : (List Nat × List Nat) × Bool => step (some x.1) x.2) := by
  let A := (List Nat × List Nat) × Bool
  have hx : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hz : Primrec (fun p : A => (p.1.1.getD 0 0)) := (Primrec.list_getD 0).comp hx (Primrec.const 0)
  have hr : Primrec (fun p : A => (p.1.2.getD 0 0)) := (Primrec.list_getD 0).comp hs (Primrec.const 0)
  have hl : Primrec (fun p : A => (p.1.2.getD 1 0)) := (Primrec.list_getD 0).comp hs (Primrec.const 1)
  have hn : Primrec (fun p : A => node 4 (p.1.2.getD 1 0) (p.1.2.getD 0 0)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hl hr)) (Primrec.const 4)
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

theorem stepProgram : Primrec (fun x : State × Bool => step x.1 x.2) := by
  have hsome : Primrec₂ (fun x : State × Bool => fun s : List Nat × List Nat => step (some s) x.2) :=
    (payloadStep.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  apply (Primrec.option_casesOn Primrec.fst (Primrec.const none) hsome).of_eq
  rintro ⟨s,b⟩
  cases s <;> rfl

theorem runProgram : Primrec (fun x : List Bool × State => run x.1 x.2) :=
  Primrec.list_foldl Primrec.fst Primrec.snd (stepProgram.comp Primrec.snd).to₂

theorem finishProgram : Primrec finish := by
  have hbody : Primrec (fun p : List Nat × List Nat =>
      if p.1.length=0 ∧ p.2.length=1 then some (p.2.getD 0 0) else none) :=
    Primrec.ite
      ((Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0)).and
       (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1)))
      (Primrec.option_some.comp ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)))
      (Primrec.const none)
  apply (Primrec.option_casesOn Primrec.id (Primrec.const none)
    (hbody.comp Primrec.snd).to₂).of_eq
  intro s
  cases s with
  | none => rfl
  | some p =>
    rcases p with ⟨xs,stack⟩
    cases xs <;> cases stack with
    | nil => rfl
    | cons y ys => cases ys <;> rfl

theorem expandProgram : Primrec (fun x : List Bool × List Nat => expandCode x.1 x.2) :=
  finishProgram.comp (runProgram.comp (Primrec.fst.pair
    (Primrec.option_some.comp (Primrec.snd.pair (Primrec.const [])))))

theorem raw : PolicyShapeTargets.RawPrograms := ⟨stepProgram,runProgram,finishProgram,expandProgram⟩

attribute [local irreducible] expandCode selector macroCode

theorem policies : PolicyShapeTargets.PolicyPrograms := by
  intro p hp
  have hs : Computable (fun x : Nat × Nat × List Nat => selector p x.1 x.2.1) :=
    Computable.comp (f := fun y : Nat × Nat => selector p y.1 y.2)
      (g := fun x : Nat × Nat × List Nat => (x.1,x.2.1)) hp
      (Computable.fst.pair (Computable.fst.comp Computable.snd))
  have hm : Computable (fun x : Nat × Nat × List Nat => macroCode p x.1 x.2.1 x.2.2) := by
    unfold macroCode
    exact Computable.comp
      (f := fun y : List Bool × List Nat => expandCode y.1 y.2)
      (g := fun x : Nat × Nat × List Nat => (selector p x.1 x.2.1,x.2.2))
      expandProgram.to_comp (hs.pair (Computable.snd.comp Computable.snd))
  refine ⟨hm,?_⟩
  have hrep : Primrec (fun x : Nat × Nat × Nat => List.replicate x.2.1 x.2.2) := by
    apply (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).to₂).of_eq
    intro x
    simp
  apply (Computable.cond
    ((Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).to_comp)
    (Computable.const (some 0))
    (hm.comp (Computable.fst.pair
      ((Primrec.nat_sub.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 1)).pair hrep.to_comp)))).of_eq
  intro x
  simp only [PolicyShape.repeatCode, Bool.cond_eq_ite, beq_iff_eq]
end LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
