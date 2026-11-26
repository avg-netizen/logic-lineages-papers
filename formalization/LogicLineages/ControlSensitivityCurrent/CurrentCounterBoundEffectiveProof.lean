module
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundSemanticProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCounterBound

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open OriginalInput (Query context)
open ForwardTranslation

theorem tupleEnvironment_primitive : Primrec tupleEnvironment := by
  have hm : Primrec (fun xs : List Nat => xs.map Nat.succ) :=
    Primrec.list_map Primrec.id (Primrec.succ.comp Primrec.snd).to₂
  exact SourceGroundComponentEnvironment.Proof.uniformPrimitiveRecursive.2.2.comp hm

private theorem evaluators_computable (f : Nat → Nat) (hc : Computable f)
    (hf : FullAddition.Targets.SourceGrowth f) :
    Computable₂ (evaluators f) := by
  let P := List Nat × List Nat
  let elem (p : P) (i : Nat) := CurrentOrdinalEvaluation.evaluate f p.1 (p.2.getD i 0)
  have he : Computable₂ elem :=
    ((CurrentOrdinalEvaluation.effective f hc hf).comp
      ((Computable.fst.comp Computable.fst).pair
        ((Primrec.list_getD 0).to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))).to₂
  have hstep : Computable₂ (fun (p : P) (st : Nat × List Nat) => st.2 ++ [elem p st.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (he.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec (Computable.list_length.comp Computable.snd)
    (Computable.const []) hstep).of_eq
  intro p
  have e (n : Nat) : Nat.rec [] (fun i acc => acc ++ [elem p i]) n =
      (List.range n).map (elem p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.rec [] (fun i acc => acc ++ [elem p i]) n ++ [elem p n] = _
      rw [ih, List.range_succ, List.map_append]
      rfl
  rw [e]
  unfold evaluators
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, elem]
    exact congrArg (CurrentOrdinalEvaluation.evaluate f p.1)
      (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)])

private theorem compareNotes_primitive :
    Primrec (fun x : Bool × List Nat × List Nat => compareNotes x.1 x.2.1 x.2.2) := by
  let P := Bool × List Nat × List Nat
  have ha : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have hpos := positiveComparisonPrimitiveRecursive.comp (Primrec.list_tail.comp ha) (Primrec.list_tail.comp hb)
  have hcmp := rawComparisonPrimitiveRecursive.comp
    ((Primrec.list_getD 0).comp ha (Primrec.const 0)) ((Primrec.list_getD 0).comp hb (Primrec.const 0))
  have hstrict := (Primrec.eq.comp hcmp (Primrec.const 0)).decide
  have hweak := (Primrec.nat_le.comp hcmp (Primrec.const 1)).decide
  have hscalar : Primrec (fun x : P =>
      if x.1 then decide (rawComparisonCode (x.2.1.getD 0 0) (x.2.2.getD 0 0) = 0)
      else decide (rawComparisonCode (x.2.1.getD 0 0) (x.2.2.getD 0 0) ≤ 1)) := by
    apply (Primrec.cond Primrec.fst hstrict hweak).of_eq
    intro x
    cases x.1 <;> rfl
  exact Primrec.and.comp hpos hscalar

private theorem assignments_computable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) :
    Computable (assignments p) := by
  let type := SyntaxCode.typeCode Ty.ground
  have hctx : Primrec (fun q : Query => (context q).map SyntaxCode.typeCode) := by
    have h : Primrec (fun q : Query => (List.range q.1).map (fun _ => type)) :=
      Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const type).to₂
    exact h.of_eq (fun q => by simp [context, type])
  have hn := (PolicyAssignmentStatementChecks.full.2.2.2 p hp).2
  have ha : Computable (fun q : Query =>
      PolicyAssignment.assignmentCode p ((context q).map SyntaxCode.typeCode) q.2.2.1) :=
    hn.comp (hctx.to_comp.pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun q : Query =>
      PolicyAssignment.assignmentCode p ((context q).map SyntaxCode.typeCode) q.2.2.2) :=
    hn.comp (hctx.to_comp.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hpair : Computable₂ (fun (x : Query × List Nat) (b : List Nat) => some (x.2, b)) :=
    (Computable.option_some.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  exact Computable.option_bind ha (Computable.option_bind (hb.comp Computable.fst) hpair).to₂

theorem effective : CurrentCounterBoundTargets.Effective := by
  intro p hp f hc hf
  let P := Query × List Nat
  let A := List Nat × List Nat
  have ha := (assignments_computable p hp).comp (Computable.fst : Computable (fun x : P => x.1))
  have he := evaluators_computable f hc hf
  have hv : Computable (fun x : P × A => tupleEnvironment x.1.2) :=
    tupleEnvironment_primitive.to_comp.comp (Computable.snd.comp Computable.fst)
  have hl := he.comp hv (Computable.fst.comp (Computable.snd : Computable (fun x : P × A => x.2)))
  have hr := he.comp hv (Computable.snd.comp (Computable.snd : Computable (fun x : P × A => x.2)))
  have hm : Computable (fun x : P × A => x.1.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ht := compareNotes_primitive.to_comp.comp (hm.pair (hl.pair hr))
  apply (Computable.option_casesOn ha (Computable.const true) ht.to₂).of_eq
  intro x
  cases h : assignments p x.1 <;> simp only [test, h] <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentCounterBound
