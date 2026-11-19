module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionMergeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetBoxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainStatementChecks
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationProof
public import LogicLineages.OrdinalComparison.NumericUnaryChainStatementChecks
public import LogicLineages.OrdinalComparison.NumericCarrierDataSemanticProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction

open LogicLineages.OrdinalComparison (ordinalNaturalSum)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum SourceTypedPorts
open CurrentReserve (unitValue zeroUnits)
open CurrentUnaryChain (commonUnits headSum)

theorem actualCaller : CurrentGroundConstructionTargets.ActualCaller := by
  intro p Γ k C u hC
  obtain ⟨v,hv,he⟩ := CurrentSelectedCarriers.StatementChecks.literal_zero_saturation p Γ k C u hC
  have hc := (SyntaxCode.Proof.typedCheckExact Γ (Ty.curriedGround (k+1)) (SyntaxCode.encodeTerm C)).2 ⟨C,rfl⟩
  have har := (TrackedSourceInspectionCode.Proof.exactArity (Ty.curriedGround (k+1)) (k+1)).2 rfl
  have hsat := NumericCarrierData.Proof.saturate_source k C
  have hv' := CurrentGroundBudget.assignmentCode p (UnaryCarrier.saturate k C) v hv
  refine ⟨v,hv,he,?_⟩
  simp only [callerCode,hc,har,Nat.add_sub_cancel,Nat.add_one_ne_zero,if_true,if_false,
    bind,pure,Option.bind_some]
  rw [hsat,hv']
  rfl

private theorem assignedRename (p : Policy) {Γ Δ τ} (r : Renaming Γ Δ)
    (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (hv : AdmissibleAssignment.assignment p t = some v) :
    AdmissibleAssignment.assignment p (t.rename r) = some (SourceRenaming.renameVector r v) := by
  rw [SourceRenaming.Proof.assignmentNaturality,hv]
  rfl

private theorem mergedAssignment (p : Policy) {Γ} (ops : List (Operator Γ))
    (ha : ∀ op ∈ ops, op.Assigned p)
    (pair : OriginalTerm (context ops) (Ty.curriedGround 1) × OrdinalVector (context ops) 1)
    (hm : pair ∈ merged ops) : AdmissibleAssignment.assignment p pair.1 = some pair.2 := by
  induction ops with
  | nil => cases hm
  | cons op ops ih =>
    simp only [merged,List.mem_cons,List.mem_map] at hm
    rcases hm with rfl | ⟨q,hq,rfl⟩
    · exact assignedRename p (headMap op ops) op.term op.vector (ha op (by simp))
    · exact assignedRename p (shiftVariable op.privateContext) q.1 q.2
        (ih (fun v hv => ha v (by simp [hv])) q hq)

private theorem pairsAssigned (p : Policy) {Γ}
    (xs : List (OriginalTerm Γ (Ty.curriedGround 1) × OrdinalVector Γ 1))
    (ha : ∀ x ∈ xs, AdmissibleAssignment.assignment p x.1 = some x.2) :
    CurrentUnaryChain.Assigned p (xs.map Prod.fst) (xs.map Prod.snd) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact .cons (ha a (by simp)) (ih (fun x hx => ha x (by simp [hx])))

private theorem assignedUnique (p : Policy) {Γ}
    (vs : List (OriginalTerm Γ (Ty.curriedGround 1))) (ws us : List (OrdinalVector Γ 1))
    (hw : CurrentUnaryChain.Assigned p vs ws) (hu : CurrentUnaryChain.Assigned p vs us) : ws = us := by
  induction hw generalizing us with
  | nil => cases hu; rfl
  | @cons t w vs ws htw hrest ih =>
    cases hu with
    | @cons _ u _ us htu htail =>
      exact congrArg₂ List.cons (Option.some.inj (htw.symm.trans htu)) (ih us htail)

theorem unitRename (f : Nat → Nat) {Γ Δ} (r : Renaming Γ Δ) (q : OrdinalExpression Γ) :
    unitValue f (ordinalExpressionRename r q) = unitValue f q := by
  simp only [unitValue,zeroUnits]
  exact PolicyObservation.expressionNaturality f Γ Δ r (fun _ => 1) (fun _ => 1)
    (fun _ _ _ => rfl) q

private theorem mergedHeadTrace (f : Nat → Nat) {Γ} (ops : List (Operator Γ)) :
    (vectors ops).map (fun v => unitValue f (v 1)) = ops.map (fun op => unitValue f (op.vector 1)) := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [vectors,merged,List.map_cons,List.map_map,Function.comp_def,
      SourceRenaming.renameVector,unitRename] at ih ⊢
    apply congrArg (fun as : List Ordinal => unitValue f (op.vector 1) :: as)
    trans (merged ops).map (fun a => unitValue f (a.2 1))
    · apply congrArg (fun g => (merged ops).map g)
      funext a
      exact unitRename f (shiftVariable op.privateContext) (a.2 1)
    · exact ih

private theorem headSumUnit (f : Nat → Nat) {Γ} (vs : List (OrdinalVector Γ 1)) :
    headSum f (commonUnits (fun _ => 0)) vs =
      HeterogeneousUnaryAssembly.chargedSum (vs.map (fun v => unitValue f (v 1))) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ordinalNaturalSum (ordinalNaturalSum (unitValue f (v 1)) 3)
      (headSum f (commonUnits (fun _ => 0)) vs) =
      ordinalNaturalSum (unitValue f (v 1)+3)
        (HeterogeneousUnaryAssembly.chargedSum (vs.map (fun v => unitValue f (v 1))))
    rw [ih]
    rw [show ordinalNaturalSum (unitValue f (v 1)) 3 = unitValue f (v 1)+3 by
      simpa using actualNaturalSumFiniteRight (unitValue f (v 1)) 3]

theorem positiveCommonValue (f : Nat → Nat) {Γ i} (q : OrdinalExpression Γ)
    (hq : GeneratedOrdinalGrade Γ i q) (hi : 0 < i) (μ : Variable Γ .ground → Nat) :
    ParametricSourceSuccessor.denoteWith f (commonUnits μ) q = unitValue f q := by
  have hpos := (CurrentAffineHeads.positiveNoCollapse Γ i q hi hq).2
  rw [hpos f (commonUnits μ)]
  unfold unitValue
  rw [hpos f (commonUnits (fun _ => 0))]
  have hv := UnaryCarrier.Proof.positive_unit_value i q hi hq μ
  simp only [OriginalDomain.expressionValue,ScalarCarrierAccounting.unitValue] at hv
  rw [CurrentAffineHeads.sameCommonUnits,← zeroUnits] at hv
  exact hv

theorem exactSingleChain : CurrentGroundConstructionTargets.ExactSingleChain := by
  intro p f Γ ops ha
  have hs := pairsAssigned p (merged ops) (mergedAssignment p ops ha)
  change CurrentUnaryChain.Assigned p (terms ops) (vectors ops) at hs
  obtain ⟨ws,v,hws,hv,hhead⟩ := CurrentUnaryChain.StatementChecks.selected_first_field_common_units
    p f (context ops) (terms ops)
  have he := assignedUnique p (terms ops) ws (vectors ops) hws hs
  subst ws
  refine ⟨hs,v,hv,?_,?_⟩
  · have hm := exactMergedPayloads Γ ops
    have hl := (NumericUnaryChain.StatementChecks.exact_single_lambda (context ops) (terms ops)).2
    have hv' := CurrentGroundBudget.assignmentCode p (SourceUnaryChain.chainSource (terms ops)) v hv
    unfold chainCode
    rw [hm.1,hm.2.2]
    have hcode : ((merged ops).map NumericUnaryChain.pairCode).map Prod.fst =
        (terms ops).map SyntaxCode.encodeTerm := by simp [terms,List.map_map,NumericUnaryChain.pairCode,Function.comp_def]
    rw [hcode,hl,hv']
    rfl
  · obtain ⟨v',hv',hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated (context ops)
      (Ty.curriedGround 1) p (SourceUnaryChain.chainSource (terms ops))
    have same : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    intro μ
    have hunit := positiveCommonValue f (v 1) (hg 1) (by decide) μ
    rw [hunit]
    change ParametricSourceSuccessor.denoteWith f (commonUnits (fun _ => 0)) (v 1) = chargedSum f ops
    rw [hhead (fun _ => 0),headSumUnit,mergedHeadTrace]
    rfl

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction
