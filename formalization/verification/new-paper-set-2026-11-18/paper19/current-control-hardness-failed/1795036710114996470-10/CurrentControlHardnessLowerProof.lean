module
public import LogicLineages.ControlSensitivityCurrent.CurrentControlHardnessTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationProof
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonProof
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentControlHardness

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan GroundEquivalence

theorem raw_canonical (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (n : Nat) (a b : OriginalTerm (List.replicate n Ty.ground) .ground) :
    rawMember strict p f (SourceMachineQueryCode.pack (n, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b)) ↔
      queryHolds strict p f a b := by
  constructor
  · rintro ⟨m, l, r, hd, h⟩
    rw [SourceMachineQueryCode.Proof.roundtrip] at hd
    have he := Option.some.inj hd
    have hm : n = m := congrArg Prod.fst he
    subst m
    have hl := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun c : SourceMachineQueryCode.Query => c.2.1) he)
    have hr := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun c : SourceMachineQueryCode.Query => c.2.2) he)
    cases hl
    cases hr
    exact h
  · intro h
    exact ⟨n, a, b, SourceMachineQueryCode.Proof.roundtrip _, h⟩

theorem raw_typed (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (Γ : List Ty) (hg : SourceMachineRawValuations.AllGround Γ) (a b : OriginalTerm Γ .ground) :
    rawMember strict p f (SourceMachineQueryCode.pack (Γ.length, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b)) ↔
      queryHolds strict p f a b := by
  have hc := SourceGammaCodedReduction.Proof.ground_context Γ hg
  generalize hn : Γ.length = n at hc
  subst Γ
  simpa only [List.length_replicate] using raw_canonical strict p f n a b

private theorem strict_pair (b e : Nat) :
    ((dagPair true b e).1.term,(dagPair true b e).2.term) =
      ((SourceMachineAggregateBridge.aggregate b e).2,(SourceMachineAggregateBridge.aggregate b e).1) := by
  let r := compile (SourceMachineConjunctionPlan.plan b e)
  have h := (ScopedDAG.Proof.aggregate r.context r.forest).1
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

private theorem weak_pair (b e : Nat) :
    ((dagPair false b e).1.term,(dagPair false b e).2.term) =
      (ParametricLiteralWeakWrapper.constantApply (SourceMachineAggregateBridge.aggregate b e).2,
        ParametricLiteralWeakWrapper.identityApply (SourceMachineAggregateBridge.aggregate b e).1) := by
  have h := strict_pair b e
  change (ParametricLiteralWeakWrapper.constantApply (dagPair true b e).1.term,
    ParametricLiteralWeakWrapper.identityApply (dagPair true b e).2.term) = _
  rw [congrArg Prod.fst h, congrArg Prod.snd h]

private theorem exact_output (strict : Bool) (b e : Nat) :
    output strict b e = SourceMachineQueryCode.pack ((ctx b e).length,
      SyntaxCode.encodeTerm (dagPair strict b e).1.term, SyntaxCode.encodeTerm (dagPair strict b e).2.term) := by
  cases strict
  · change SourceGammaWeakCodedReduction.output b e = _
    unfold SourceGammaWeakCodedReduction.output
    rw [(SourceGammaWeakCodedReduction.Proof.exactGeneratedQuery b e).1,
      congrArg Prod.fst (weak_pair b e), congrArg Prod.snd (weak_pair b e)]
  · change SourceMachineQueryCode.output b e = _
    unfold SourceMachineQueryCode.output
    rw [(SourceMachineQueryCode.Proof.exactPackaging.2 b e).1,
      congrArg Prod.fst (strict_pair b e), congrArg Prod.snd (strict_pair b e)]
    rfl

private theorem weak_at (b e : Nat) (p : AdmissibleSum.Policy)
    (ρ : Variable (ctx b e) .ground → Nat) :
    PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ)
      (dagPair false b e).1.term ≤
    PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ)
      (dagPair false b e).2.term ↔
    ¬ PolicyPlan.ResultHolds p (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ := by
  let f := SourceMachineControlNonperiodicity.gamma b
  let es := (compile (SourceMachineConjunctionPlan.plan b e)).forest
  have hf := CurrentMachinePlan.gamma_growth b
  rw [congrArg Prod.fst (weak_pair b e), congrArg Prod.snd (weak_pair b e)]
  unfold ParametricLiteralWeakWrapper.constantApply ParametricLiteralWeakWrapper.identityApply
  rw [PolicyOrderWrapper.constantValue f hf, PolicyOrderWrapper.identityValue f hf]
  have hm : StrictMono (PolicyCollision.g f) := by
    intro x y h
    exact Nat.add_lt_add_right (CurrentOrdinalEvaluation.growth_mono f hf (Nat.add_lt_add_right h 2)) 1
  rw [hm.le_iff_le, PolicyProgramComparison.holds_raw]
  have ha := FullAggregate.completeAggregate.2.2.2 f hf p (ctx b e) (inputs ρ) (ScopedDAG.equations es)
  change PolicyCollision.rawScalar p f (inputs ρ) (SourceAggregateCompletion.aggregate (ScopedDAG.equations es)).2 + 5 ≤
    PolicyCollision.rawScalar p f (inputs ρ) (SourceAggregateCompletion.aggregate (ScopedDAG.equations es)).1 + 3 ↔ _
  constructor
  · intro h he
    have heq := ha.2.1.mpr he
    omega
  · intro h
    have hd := ha.2.2 h
    omega

private theorem compares_iff (strict : Bool) (b e : Nat) (p : AdmissibleSum.Policy) :
    queryHolds strict p (SourceMachineControlNonperiodicity.gamma b) (dagPair strict b e).1.term
      (dagPair strict b e).2.term ↔ ¬ SourceBlankMachineSimulation.Halts e := by
  have ht := CurrentMachinePlan.compiled_halting b e p
  have key (ρ : Variable (ctx b e) .ground → Nat) :
      (if strict then
        PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ) (dagPair strict b e).1.term <
        PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ) (dagPair strict b e).2.term
      else
        PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ) (dagPair strict b e).1.term ≤
        PolicyCollision.rawScalar p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ) (dagPair strict b e).2.term) ↔
        ¬ PolicyPlan.ResultHolds p (SourceMachineControlNonperiodicity.gamma b)
          (compile (SourceMachineConjunctionPlan.plan b e)) ρ := by
    cases strict
    · exact weak_at b e p ρ
    · exact PolicyProgramComparison.strict_at _ (CurrentMachinePlan.gamma_growth b) p _ ρ
  rw [← not_congr ht, not_exists]
  cases strict
  · exact forall_congr' key
  · exact forall_congr' key

theorem exactLowering : CurrentControlHardnessTargets.ExactLowering := by
  intro b p strict
  have hp : Primrec (output strict b) := by
    cases strict
    · exact SourceGammaWeakCodedReduction.Proof.uniformPrimitiveRecursive.2.comp (Primrec.const b) Primrec.id
    · exact SourceMachineQueryCode.Proof.uniformPrimitiveRecursive.2.2.2.comp (Primrec.const b) Primrec.id
  refine ⟨hp, fun e => ?_⟩
  have hclass : SourceGammaRestrictedReduction.RestrictedSyntax (output strict b e) := by
    cases strict
    · exact (SourceGammaWeakCodedReduction.Proof.exactGeneratedQuery b e).2
    · exact SourceGammaRestrictedReduction.Proof.generatedRange b e
  refine ⟨exact_output strict b e, hclass, ?_⟩
  unfold member
  rw [and_iff_right hclass, exact_output,
    raw_typed strict p _ _ (SourceMachineRawValuations.Proof.groundContexts.2 b e)]
  exact compares_iff strict b e p

theorem actualDAGBound : CurrentControlHardnessTargets.ActualDAGBound := by
  intro b e strict
  let r := compile (SourceMachineConjunctionPlan.plan b e)
  have hs := SourceMachineConjunctionPlan.Proof.exactCompiledBounds b e
  have ha := ScopedDAG.Proof.aggregate r.context r.forest
  have hw := PolicyProgramComparison.weight_identity r.forest
  change ScopedDAG.weight r.forest = 2*r.nodes + 8*r.forest.length + 1 at hw
  have hb : ScopedDAG.weight r.forest + 3 ≤ 250 * (e + 4 * SourceMachineConjunctionPlan.bits b + 27) + 24 := by
    rw [hw]
    change r.nodes ≤ _ ∧ r.forest.length ≤ _ ∧ _ at hs
    omega
  cases strict
  · change (ScopedDAG.aggregate r.forest).2.specs.length + 3 ≤ _ ∧
      (ScopedDAG.aggregate r.forest).1.specs.length + 3 ≤ _
    rw [ha.2.1, ha.2.2]
    exact ⟨hb, hb⟩
  · change (ScopedDAG.aggregate r.forest).2.specs.length ≤ _ ∧
      (ScopedDAG.aggregate r.forest).1.specs.length ≤ _
    rw [ha.2.1, ha.2.2]
    omega

end LogicLineages.ControlSensitivityCurrent.CurrentControlHardness
