module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCodePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionPositiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteAnchorProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open CurrentDecisionEmitter
open RawSourceDAG (Code)
open RawSourceDAG.InputCompiler (InputCode)

private theorem counterComputable (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (h : Computable (CurrentAbsolute.anchor p f)) : Computable (counterCode p f) := by
  have qa : Computable (fun q : QueryCode => q.2.1) := Computable.fst.comp Computable.snd
  have qb : Computable (fun q : QueryCode => q.2.2) := Computable.snd.comp Computable.snd
  have qL := probeCodesPrimitive.to_comp.comp (Computable.const false) qa
  have qR := probeCodesPrimitive.to_comp.comp (Computable.const true) qb
  have a := factorCodePrimitive.to_comp.comp qa
  have b := factorCodePrimitive.to_comp.comp qb
  have A := h.comp qa
  have B := h.comp qb
  have plus {g k : QueryCode → Nat} (hg : Computable g) (hk : Computable k) :
      Computable (fun q => g q + k q) := Primrec.nat_add.to_comp.comp hg hk
  have num (n : Nat) : Computable (fun _ : QueryCode => n) := Computable.const n
  have l := plus a (num 5)
  have r := plus b (num 5)
  have left := observeStepsPrimitive.to_comp.comp
    ((Computable.fst.comp qL).pair ((Computable.snd.comp qL).pair
      ((num 0).pair ((num 1).pair ((num 4).pair (a.pair A))))))
  have rb₁ := liftCodePrimitive.to_comp.comp l (Computable.fst.comp qR)
  have rb₂ := liftCodePrimitive.to_comp.comp l (Computable.snd.comp qR)
  have right := observeStepsPrimitive.to_comp.comp
    (rb₁.pair (rb₂.pair ((plus (num 2) l).pair ((plus (num 3) l).pair
      ((plus (num 5) l).pair (b.pair B))))))
  have portsL := (plus (plus a (num 4)) r).pair
    ((plus (plus a (num 3)) r).pair ((plus (num 2) r).pair r))
  have portsR := (plus b (num 4)).pair
    ((plus b (num 3)).pair ((num 2).pair (num 0)))
  have rows := rowCodesPrimitive.to_comp.comp
    ((Computable.fst : Computable (fun q : QueryCode => q.1)).pair
      (portsL.pair (portsR.pair ((plus (plus (num 4) l) r).pair (plus (plus (num 5) l) r)))))
  exact (Primrec.list_append.to_comp.comp (Primrec.list_append.to_comp.comp left right)
    (Computable.fst.comp rows)).pair (Computable.snd.comp rows)

theorem effective : CurrentDecisionTargets.Effective := by
  refine ⟨CurrentCompiler.effective.2,?_⟩
  intro p hp f hc hf
  have htest := positive_computable p hp
  have hcounter := counterComputable p f (CurrentAbsolute.anchorEffective p hp f hc hf)
  have branch : Computable (fun q : QueryCode =>
      if positiveTest p q then counterCode p f q else CurrentAttainment.truthCode) := by
    apply (Computable.cond htest hcounter (Computable.const CurrentAttainment.truthCode)).of_eq
    intro q
    cases e : positiveTest p q <;> simp [e]
  have arity : Computable (fun q : QueryCode => q.2.1.1.length + 6) :=
    (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.snd : Primrec (fun q : QueryCode => q.2)))))
      (Primrec.const 6)).to_comp
  have emit : Computable (toArithmetic p f) := arity.pair branch
  exact ⟨emit,CurrentCompiler.effective.2.comp emit⟩

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
