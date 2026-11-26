module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeProof
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG (Code)
open RawSourceDAG.InputCompiler (InputCode InputStep)
open CurrentDecisionEmitter
open RawSourceDAG.Operations
open RawSourceDAG.BinaryPlanCompiler (prefixTable prefix_table_primitive)

private theorem replicateZero : Primrec (fun n : Nat => List.replicate n 0) := by
  have h : Primrec (fun n : Nat => (List.range n).map (fun _ => (0 : Nat))) :=
    Primrec.list_map Primrec.list_range (Primrec.const 0).to₂
  exact h.of_eq (fun n => by simp)

theorem liftCodePrimitive : Primrec₂ liftCode := by
  let P := Nat × Code
  have hc : Primrec (fun x : P => x.2) := Primrec.snd
  have hΓ := Primrec.fst.comp hc
  have hpre := prefix_table_primitive.comp (Primrec.fst.pair hΓ)
  exact rename_code_primitive.comp ((Primrec.list_append.comp (replicateZero.comp Primrec.fst) hΓ).pair (hpre.pair hc))

theorem probeCodesPrimitive : Primrec₂ probeCodes := by
  let P := Bool × Code
  have hc : Primrec (fun x : P => x.2) := Primrec.snd
  have hΓ := Primrec.fst.comp hc
  have ctx2 := Primrec.list_append.comp (Primrec.const ([0,0] : List Nat)) hΓ
  have ctx6 := Primrec.list_append.comp (Primrec.const (List.replicate 6 (0 : Nat))) hΓ
  have aux : Primrec (fun x : P => if x.1 then [2,3] else ([0,1] : List Nat)) := by
    exact (Primrec.cond Primrec.fst (Primrec.const ([2,3] : List Nat)) (Primrec.const [0,1])).of_eq
      (fun x => by cases x.1 <;> rfl)
  have table := Primrec.list_append.comp aux (prefix_table_primitive.comp ((Primrec.const 6).pair hΓ))
  have hleft := CurrentProbeCode.effective.2.comp (liftCodePrimitive.comp (Primrec.const 2) hc) (Primrec.const 0)
  have hclose := rename_code_primitive.comp
    (ctx2.pair ((Primrec.const []).pair (CurrentProbeCode.effective.1.comp hc)))
  have hright := CurrentProbeCode.effective.2.comp hclose (Primrec.const 1)
  exact (rename_code_primitive.comp (ctx6.pair (table.pair hleft))).pair
    (rename_code_primitive.comp (ctx6.pair (table.pair hright)))

theorem factorCodePrimitive : Primrec factorCode := by
  have ht : Primrec (fun d : Code => d.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp ht) (Primrec.const 1)))
    (Primrec.const 1)

private theorem addStepsPrimitive : Primrec₂ CurrentAttainment.addSteps := by
  let P := Nat × Nat
  have hi : Primrec (fun p : P × Nat => p.1.2 + p.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const 1)
  have hstep : Primrec (fun p : P × Nat => (((6,1,p.1.2+p.2+1),none) : InputStep)) :=
    ((Primrec.const 6).pair ((Primrec.const 1).pair hi)).pair (Primrec.const none)
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (fun p : P => p.1))) hstep.to₂

private theorem stepPlain {P : Type} [Primcodable P] {tag a b : P → Nat}
    (ht : Primrec tag) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun p => (((tag p,a p,b p),none) : InputStep)) :=
  (ht.pair (ha.pair hb)).pair (Primrec.const none)

theorem observeStepsPrimitive : Primrec (fun p : Code × Code × Nat × Nat × Nat × Nat × Nat =>
    observeSteps p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let P := Code × Code × Nat × Nat × Nat × Nat × Nat
  have h₁ : Primrec (fun p : P => p.2) := Primrec.snd
  have h₂ := Primrec.snd.comp h₁
  have h₃ := Primrec.snd.comp h₂
  have h₄ := Primrec.snd.comp h₃
  have h₅ := Primrec.snd.comp h₄
  have ha : Primrec (fun p : P => p.1) := Primrec.fst
  have hb := Primrec.fst.comp h₁
  have hx := Primrec.fst.comp h₂
  have hy := Primrec.fst.comp h₃
  have hv := Primrec.fst.comp h₄
  have hf := Primrec.fst.comp h₅
  have hc := Primrec.snd.comp h₅
  have s₁ : Primrec (fun p : P => (((8,0,0),some p.1) : InputStep)) :=
    (Primrec.const (8,0,0)).pair (Primrec.option_some.comp ha)
  have s₂ := (Primrec.const ((8,0,0) : Nat × Nat × Nat)).pair
    (Primrec.option_some.comp (liftCodePrimitive.comp (Primrec.const 1) hb))
  have s₃ := stepPlain (Primrec.const 6) (Primrec.nat_add.comp hx (Primrec.const 3)) (Primrec.const 0)
  have sf := addStepsPrimitive.comp hf (Primrec.nat_add.comp hv (Primrec.const 3))
  have s₄ := stepPlain (Primrec.const 7) (Primrec.nat_mul.comp hf hc) (Primrec.const 0)
  have s₅ := stepPlain (Primrec.const 6) (Primrec.const 1)
    (Primrec.nat_add.comp hy (Primrec.nat_add.comp hf (Primrec.const 5)))
  have pre := Primrec.list_cons.comp s₁ (Primrec.list_cons.comp s₂
    (Primrec.list_cons.comp s₃ (Primrec.const [])))
  have post := Primrec.list_cons.comp s₄ (Primrec.list_cons.comp s₅ (Primrec.const []))
  exact Primrec.list_append.comp (Primrec.list_append.comp pre sf) post

theorem rowCodesPrimitive : Primrec (fun p : Bool × Indices × Indices × Nat × Nat =>
    rowCodes p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Bool × Indices × Indices × Nat × Nat
  have h₁ : Primrec (fun p : P => p.2) := Primrec.snd
  have h₂ := Primrec.snd.comp h₁
  have h₃ := Primrec.snd.comp h₂
  have ha := Primrec.fst.comp h₁
  have hb := Primrec.fst.comp h₂
  have hv := Primrec.fst.comp h₃
  have hw := Primrec.snd.comp h₃
  have sTag : Primrec (fun p : P => if p.1 then (1 : Nat) else 2) := by
    exact (Primrec.cond Primrec.fst (Primrec.const (1 : Nat)) (Primrec.const 2)).of_eq
      (fun x => by cases x.1 <;> rfl)
  have plus {g : P → Nat} (h : Primrec g) : Primrec (fun p => g p+1) :=
    Primrec.nat_add.comp h (Primrec.const 1)
  have sA (x : P → Indices) (hx : Primrec x) :
      Primrec (fun p => (((0,(x p).1+1,(x p).2.1+1),none) : InputStep)) :=
    stepPlain (Primrec.const 0) (plus (Primrec.fst.comp hx)) (plus (Primrec.fst.comp (Primrec.snd.comp hx)))
  have sB (x : P → Indices) (hx : Primrec x) :
      Primrec (fun p => (((0,(x p).2.2.1+1,(x p).2.2.2+1),none) : InputStep)) :=
    stepPlain (Primrec.const 0) (plus (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hx))))
      (plus (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hx))))
  have sC := stepPlain sTag (plus hw) (plus hv)
  have post : Primrec (fun _ : P => ([((4,3,4),none),((4,2,3),none),
      ((4,0,1),none),((4,0,3),none)] : List InputStep)) := Primrec.const _
  exact (Primrec.list_cons.comp (sA _ ha) (Primrec.list_cons.comp (sB _ ha) (Primrec.list_cons.comp (sA _ hb)
    (Primrec.list_cons.comp (sB _ hb) (Primrec.list_cons.comp sC post))))).pair (Primrec.const 0)

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
