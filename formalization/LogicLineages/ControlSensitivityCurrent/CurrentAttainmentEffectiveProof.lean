module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentPrefixProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.FullStandardResiduesProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent LogicLineages.PermittedControl
open RawSourceDAG.InputCompiler (InputCode InputStep)

private theorem bound_primitive : Primrec₂ bound := by
  let P := Nat × Request
  have hm : Primrec (fun x : P => x.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : P => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.nat_max.comp Primrec.fst (Primrec.nat_sub.comp hm (Primrec.const 100))) hp)
    (Primrec.nat_mod.comp ha hp)

private theorem residue_primitive : Primrec residue := by
  have hm : Primrec (fun q : Request => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun q : Request => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_mod.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp hr (FullStandardResidues.completeResidues.2.1.comp hm))
    (Primrec.nat_sub.comp hm (Primrec.const 1))) hm

private theorem addSteps_primitive : Primrec₂ addSteps := by
  let P := Nat × Nat
  have hh : Primrec (fun p : P × Nat => p.1.2 + p.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const 1)
  have hstep : Primrec (fun p : P × Nat => (((6,1,p.1.2+p.2+1),none) : InputStep)) :=
    ((Primrec.const 6).pair ((Primrec.const 1).pair hh)).pair (Primrec.const none)
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (fun p : P => p.1))) hstep.to₂

private theorem tailCode_primitive : Primrec (fun p : RawSourceDAG.Code × Nat × Request =>
    tailCode p.1 p.2.1 p.2.2) := by
  let P := RawSourceDAG.Code × Nat × Request
  have hc : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp hq
  have hm : Primrec (fun p : P => p.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hq))
  have hb := Primrec.nat_sub.comp (bound_primitive.comp hc hq) hc
  have hs := residue_primitive.comp hq
  have mk1 : Primrec (fun p : P => (((7,bound p.2.1 p.2.2-p.2.1,0),none) : InputStep)) :=
    ((Primrec.const 7).pair (hb.pair (Primrec.const 0))).pair (Primrec.const none)
  have mk2 : Primrec (fun p : P => (((9,0,0),some p.1) : InputStep)) :=
    (Primrec.const (9,0,0)).pair (Primrec.option_some.comp Primrec.fst)
  have mk3 : Primrec (fun p : P => (((7,residue p.2.2,0),none) : InputStep)) :=
    ((Primrec.const 7).pair (hs.pair (Primrec.const 0))).pair (Primrec.const none)
  have mk4 : Primrec (fun p : P => (((0,p.2.2.2.2.1+2,1),none) : InputStep)) :=
    ((Primrec.const 0).pair ((Primrec.nat_add.comp hm (Primrec.const 2)).pair (Primrec.const 1))).pair (Primrec.const none)
  have hsingle {f : P → InputStep} (hf : Primrec f) : Primrec (fun p => [f p]) :=
    Primrec.list_cons.comp hf (Primrec.const [])
  have hf := Primrec.list_append.comp (hsingle mk1) (addSteps_primitive.comp hp (Primrec.const 1))
  have hh := Primrec.list_cons.comp mk2 (hsingle mk3)
  have hl := addSteps_primitive.comp hm (Primrec.nat_add.comp hp (Primrec.const 4))
  exact (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp hf hh) hl)
    (hsingle mk4)).pair (Primrec.const 0)

private theorem prefix_computable : Computable (fun p : Nat × Request × Nat => finitePrefix p.1 p.2.1 p.2.2) := by
  let P := Nat × Request × Nat
  let hit (p : P) (t : Nat) := decide (rawNormCode p.1 ≤ t ∧
    Nat.ModEq p.2.1.1 t p.2.1.2.1 ∧ Nat.ModEq p.2.1.2.2.1 (count p.1 t) p.2.1.2.2.2)
  have head : Primrec (fun x : P × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  have req : Primrec (fun x : P × Nat => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have pCode := Primrec.fst.comp req
  have residues := Primrec.snd.comp req
  have aCode := Primrec.fst.comp residues
  have mCode := Primrec.fst.comp (Primrec.snd.comp residues)
  have rCode := Primrec.snd.comp (Primrec.snd.comp residues)
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp head
  have hvalid := (Primrec.nat_le.comp hnorm (Primrec.snd : Primrec (fun x : P × Nat => x.2))).decide
  have hpEq := (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd pCode)
    (Primrec.nat_mod.comp aCode pCode)).decide
  have hd := count_computable.comp head.to_comp (Computable.snd : Computable (fun x : P × Nat => x.2))
  have hmEq := (Primrec.beq : Primrec₂ ((· == ·) : Nat → Nat → Bool)).to_comp.comp
    (Primrec.nat_mod.to_comp.comp hd mCode.to_comp) ((Primrec.nat_mod.comp rCode mCode).to_comp)
  have hhit : Computable₂ hit := by
    apply (Primrec.and.to_comp.comp hvalid.to_comp
      (Primrec.and.to_comp.comp hpEq.to_comp hmEq)).of_eq
    intro x
    simp [hit, Nat.ModEq, Bool.beq_eq_decide_eq]
  have hbody : Computable₂ (fun (p : P) (st : Nat × Bool) => st.2 || hit p st.1) :=
    (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
      (hhit.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec (Computable.snd.comp Computable.snd) (Computable.const false) hbody).of_eq
  intro p
  have eq (n : Nat) : Nat.rec false (fun i prev => prev || hit p i) n =
      (List.range n).any (hit p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((Nat.rec false (fun i prev => prev || hit p i) n) || hit p n) = _
      rw [ih, List.range_succ, List.any_append]
      simp
  exact eq p.2.2

private theorem values_computable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) :
    Computable (headCode p) ∧ Computable (offset p) := by
  have ha := (PolicyAssignmentStatementChecks.full.2.2.2 p hp).2
  have ht : Computable (digits p) := (Primrec.option_getD.to_comp.comp
    (ha.comp ((Computable.const []).pair CurrentTreeCode.effective.to_comp)) (Computable.const []))
  have he : Computable (fun x : List Nat × Nat => CurrentOrdinalEvaluation.evaluate Phi x.1 x.2) :=
    CurrentOrdinalEvaluation.effective Phi Phi_computable standard_growth
  have harg (j : Nat) : Computable (fun h => CurrentOrdinalEvaluation.evaluate Phi [] ((digits p h).getD j 0)) :=
    he.comp ((Computable.const []).pair ((Primrec.list_getD 0).to_comp.comp ht (Computable.const j)))
  have hhead : Computable (headCode p) :=
    encodedNaturalProductPrimitiveRecursive.to_comp.comp (Computable.const CurrentOrdinalEvaluation.omegaCode) (harg 1)
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).to_comp.comp hhead
  have hfinite := (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).to_comp.comp (harg 0)
  exact ⟨hhead, Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hnorm hfinite) (Computable.const 1)⟩

theorem efficient_run (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) : Computable (run p) := by
  let P := RawSourceDAG.Code × Request
  have hhead : Computable (fun x : P => headCode p x.1) :=
    (values_computable p hp).1.comp Computable.fst
  have hcost : Computable (fun x : P => offset p x.1) :=
    (values_computable p hp).2.comp Computable.fst
  have hq : Computable (fun x : P => x.2) := Computable.snd
  have hb := bound_primitive.to_comp.comp hcost hq
  have hpre := prefix_computable.comp (hhead.pair (hq.pair hb))
  have htail := tailCode_primitive.to_comp.comp (Computable.fst.pair (hcost.pair hq))
  have hsel : Computable (fun x : P => select (headCode p x.1) (offset p x.1) x.1 x.2) := by
    apply (Computable.cond hpre (Computable.const truthCode) htail).of_eq
    intro x
    cases h : finitePrefix (headCode p x.1) x.2 (bound (offset p x.1) x.2) <;>
      simp [select, h]
  exact CurrentCompiler.effective.2.comp ((Computable.const 2).pair hsel)

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
