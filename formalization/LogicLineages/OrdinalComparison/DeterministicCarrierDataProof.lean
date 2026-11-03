module
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataTargets
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.Proof
open ScalarAnnotationData ScalarCarrierAccounting AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem saturation_assigned {Γ} (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
    (hu : assignment OrdinalSyntax.defaultPolicy t = some u) :
    assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate r t) = some (saturateVector r u) := by
  cases r with
  | zero => exact hu
  | succ r =>
    apply saturation_assigned r (.app t .zeroC)
    change (assignment OrdinalSyntax.defaultPolicy t).bind
      (fun v => some (application OrdinalSyntax.defaultPolicy v (fun _ => .one))) = _
    rw [hu]
    rfl
termination_by r

theorem exactSaturation : Targets.ExactSaturation := by
  intro Γ r t u hu
  have hv := saturation_assigned r t u hu
  obtain ⟨v,hv',he⟩ := UnaryCarrier.Proof.saturate_assignment r t u hu
  have eqv : v = saturateVector r u := Option.some.inj (hv'.symm.trans hv)
  exact ⟨hv,eqv ▸ he⟩

theorem carrier_assigned {k Γ} (op : Operator (Ty.curriedGround (k+1) :: Γ))
    (hop : assignment OrdinalSyntax.defaultPolicy op.source = some op.vector) :
    assignment OrdinalSyntax.defaultPolicy (carrierData op).source = some (carrierData op).vector := by
  have hr : assignment OrdinalSyntax.defaultPolicy (op.source.rename UnaryCarrier.renameTracked) =
      some (SourceRenaming.renameVector UnaryCarrier.renameTracked op.vector) := by
    rw [SourceRenaming.Proof.assignmentNaturality,hop]
    rfl
  have hs := saturation_assigned op.arity _ _ hr
  change assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.closeGround
    (UnaryCarrier.saturate op.arity (op.source.rename UnaryCarrier.renameTracked))) = _
  rw [UnaryCarrier.closeGround,GroundClosing.StatementChecks.assignmentNaturality,hs]
  rfl

theorem exactCarrierData : Targets.ExactCarrierData := by
  intro k Γ op hop
  have ha := carrier_assigned op hop
  have hn := UnaryCarrier.Proof.carrier_no_ground op.source
  obtain ⟨u,w,v,hu,hw,hv,heq,hscalar,hvalue⟩ := UnaryCarrier.Proof.actualCarrier Γ k op.arity op.source
  have eu : u = op.vector := Option.some.inj (hu.symm.trans hop)
  have ev : v = (carrierData op).vector := Option.some.inj (hv.symm.trans ha)
  subst u
  rw [ev] at hvalue
  have hc : ∀ ρ μ,
      expressionValue (UnitObservation.substitution μ) (carrierData op).head =
        expressionValue (UnitObservation.substitution ρ) op.head := by
    intro ρ μ
    exact hvalue ρ μ
  refine ⟨ha,hn,?_,hc⟩
  obtain ⟨v,hv,hg⟩ := actualAdmissibleAssignmentGenerated _ _ OrdinalSyntax.defaultPolicy (carrierData op).source
  have ev : v = (carrierData op).vector := Option.some.inj (hv.symm.trans ha)
  subst v
  obtain ⟨u,hu,hgu⟩ := actualAdmissibleAssignmentGenerated _ _ OrdinalSyntax.defaultPolicy op.source
  have eu : u = op.vector := Option.some.inj (hu.symm.trans hop)
  subst u
  have hleft := UnaryCarrier.Proof.positive_unit_value 1 (carrierData op).head (by decide)
    (hg (UnaryCarrier.headIndex 0)) (fun _ => 0)
  have hright := UnaryCarrier.Proof.positive_unit_value 1 op.head (by decide)
    (hgu (UnaryCarrier.headIndex op.arity)) (fun _ => 0)
  exact hleft.symm.trans ((hc (fun _ => 0) (fun _ => 0)).trans hright)

theorem exactCarrierList : Targets.ExactCarrierList := by
  intro k Γ ops hops
  refine ⟨List.length_map _,?_,?_⟩
  · change (ops.map carrierData).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro op hm
    exact (exactCarrierData k Γ op (hops op hm)).2.2.1
  · intro op hm
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hm
    have h := exactCarrierData k Γ old (hops old hold)
    exact ⟨h.1,h.2.1⟩
end LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.Proof
