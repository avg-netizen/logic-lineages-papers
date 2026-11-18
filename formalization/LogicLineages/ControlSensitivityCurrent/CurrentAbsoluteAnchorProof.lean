module
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeProof
public import LogicLineages.ControlSensitivityCurrent.GenericScalarProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverAnchorProof
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsolute

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open GroundEquivalence AdmissibleAssignment ParametricSourceSuccessor

theorem closing_value (f : Nat → Nat) {Γ} (hg : ∀ σ ∈ Γ, σ = Ty.ground)
    (e : OrdinalExpression Γ) (ν : OrdinalComponent [] → Ordinal) :
    denoteWith f ν (GroundClosing.expression (AbsoluteObserver.closingMap hg) e) =
      denoteWith f (fun _ => 1) e := by
  induction e with
  | var c => simp only [GroundClosing.expression, substitute, AbsoluteObserver.Proof.closing_component, denoteWith]
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [GroundClosing.expression, substitute, denoteWith] at *
    rw [iha, ihb]

theorem closure_assignment (p : AdmissibleSum.Policy) {Γ τ} (hg : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level) (hv : assignment p t = some v) :
    assignment p (AbsoluteObserver.close hg t) = some (GroundClosing.vector (AbsoluteObserver.closingMap hg) v) := by
  unfold AbsoluteObserver.close
  rw [GroundClosing.Proof.assignmentNaturality, hv]
  rfl

theorem scalar_total (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ τ) : ∃ v, 0 < v ∧ Scalar p f ρ t v := by
  obtain ⟨v, hv, _, hg⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ τ t
  have hyp := GenericScalar.generatedPositiveFinite f Γ ρ 0 (v 0) (hg 0)
  obtain ⟨n, hn⟩ := hyp.2 rfl
  have hp := hyp.1
  rw [hn] at hp
  exact ⟨n, by exact_mod_cast hp, v, hv, hn⟩

theorem scalar_unique (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ τ) (v w : Nat)
    (hv : Scalar p f ρ t v) (hw : Scalar p f ρ t w) : v = w := by
  obtain ⟨a,ha,hva⟩ := hv
  obtain ⟨b,hb,hvb⟩ := hw
  rw [ha] at hb
  cases Option.some.inj hb
  exact_mod_cast hva.symm.trans hvb

theorem anchorExact : CurrentAbsoluteTargets.AnchorExact := by
  intro p f hf Γ τ hg d
  let code := RawSourceDAG.encode ⟨Γ,τ,d⟩
  let env := SourceGroundComponentEnvironment.environment (List.replicate Γ.length 1)
  obtain ⟨v, hv, he, hgrade⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ τ d.term
  have hlookup (c : OrdinalComponent Γ) : env.getD (OrdinalSyntax.componentCode c) 0 = 1 := by
    have h := SourceGroundComponentEnvironment.Proof.typedLookup Γ (List.replicate Γ.length 1) hg
      (by simp) c
    have hi := SourceTypedPortsProof.typedVariableIndex.1 Γ c.1 c.2.1
    rw [h]
    simp only [SourceGroundComponentEnvironment.rawValuation, List.getD_eq_getElem?_getD, List.getElem?_replicate,
      if_pos hi, Option.getD_some]
  obtain ⟨a, ha, har⟩ := CurrentOrdinalEvaluation.calibration f hf _ OrdinalSyntax.componentCode
    (v 0) env (fun _ => 1) hlookup
  have grade := GenericScalar.generatedPositiveFinite f Γ (fun _ => 0) 0 (v 0) (hgrade 0)
  obtain ⟨n, hn⟩ := grade.2 rfl
  have hpos := grade.1
  rw [hn] at hpos
  have value : a.1.repr = (n : Ordinal) := by
    exact har.trans (by simpa only [Nat.zero_add] using hn)
  have hcode : anchor p f code = n := by
    change PolicyAssignment.assignmentCode p code.1 (SyntaxCode.encodeTerm d.term) =
      some (OrdinalSyntax.vectorCode v) at he
    have hd : vectorDigits p code = OrdinalSyntax.vectorCode v := by
      unfold vectorDigits
      rw [CurrentTreeCode.exactExpansion Γ τ d, he]
      rfl
    have h0 : (vectorDigits p code).getD 0 0 = OrdinalSyntax.typedCode (v 0) := by
      rw [hd]
      simp only [OrdinalSyntax.vectorCode, List.ofFn_succ, List.getD_cons_zero]
    have hlen : code.1.length = Γ.length := List.length_map _
    unfold anchor
    rw [h0, hlen]
    change encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f env
      (OrdinalSyntax.code OrdinalSyntax.componentCode (v 0))) = _
    rw [ha]
    have hfinite := (encodedFiniteCorrect a).1.mpr (value.symm ▸ Ordinal.natCast_lt_omega0 n)
    have hval := (encodedFiniteCorrect a).2 hfinite
    rw [value] at hval
    exact_mod_cast hval
  change 0 < anchor p f code ∧ _
  rw [hcode]
  refine ⟨by exact_mod_cast hpos, _, closure_assignment p hg d.term v hv, ?_⟩
  change denoteWith f _ (GroundClosing.expression (AbsoluteObserver.closingMap hg) (v 0)) = _
  rw [closing_value]
  simpa only [Nat.zero_add, Nat.cast_one] using hn

theorem anchorEffective : CurrentAbsoluteTargets.AnchorEffective := by
  intro p hp f hc hf
  have hctx : Primrec (fun d : RawSourceDAG.Code => d.1.length) := Primrec.list_length.comp Primrec.fst
  have hunits : Primrec (fun d : RawSourceDAG.Code => List.replicate d.1.length 1) := by
    have h : Primrec (fun d : RawSourceDAG.Code => (List.range d.1.length).map (fun _ => 1)) :=
      Primrec.list_map (Primrec.list_range.comp hctx) (Primrec.const 1).to₂
    exact h.of_eq (fun d => by simp)
  have henv := SourceGroundComponentEnvironment.Proof.uniformPrimitiveRecursive.2.2.comp hunits
  have ha := (PolicyAssignmentStatementChecks.full.2.2.2 p hp).2
  have hvec : Computable (vectorDigits p) :=
    Primrec.option_getD.to_comp.comp (ha.comp (Computable.fst.pair CurrentTreeCode.effective.to_comp)) (Computable.const [])
  have hal := (Primrec.list_getD 0).to_comp.comp hvec (Computable.const 0)
  have hv : Computable (fun x : List Nat × Nat => CurrentOrdinalEvaluation.evaluate f x.1 x.2) :=
    CurrentOrdinalEvaluation.effective f hc hf
  have hfinit : Primrec encodedFiniteValue := Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2
  have harg : Computable (fun d : RawSourceDAG.Code =>
      (SourceGroundComponentEnvironment.environment (List.replicate d.1.length 1),
        (vectorDigits p d).getD 0 0)) := henv.to_comp.pair hal
  apply (hfinit.to_comp.comp (hv.comp harg)).of_eq
  intro d
  rfl

end LogicLineages.ControlSensitivityCurrent.CurrentAbsolute
