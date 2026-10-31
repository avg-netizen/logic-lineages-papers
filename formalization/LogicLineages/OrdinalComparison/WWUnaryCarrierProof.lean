module
public import LogicLineages.OrdinalComparison.WWUnaryCarrierTargets
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProfileProof
public import LogicLineages.OrdinalComparison.WWGroundClosingStatementChecks
public import LogicLineages.OrdinalComparison.WWGeneratedSupportStatementChecks
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentStatementChecks
public import LogicLineages.OrdinalComparison.WWUnitObservationStatementChecks
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnaryCarrier.Proof
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem freshRename : Targets.FreshRename := by
  intro Γ σ
  refine ⟨rfl,fun _ _ => rfl,?_⟩
  intro x
  cases x <;> simp [renameTracked]

theorem saturate_assignment {Γ : List Ty} (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
    (hu : assignment OrdinalSyntax.defaultPolicy t = some u) :
    ∃ v : OrdinalVector Γ 1,
      assignment OrdinalSyntax.defaultPolicy (saturate r t) = some v ∧
      ∀ ν : OrdinalComponent Γ → Ordinal, denote ν (v 1) = denote ν (u (headIndex r)) := by
  cases r with
  | zero => exact ⟨u,hu,fun _ => rfl⟩
  | succ r =>
      let g : OrdinalVector Γ 0 := fun _ => .one
      let a := application (σ := .ground) (τ := Ty.curriedGround (r+1))
        OrdinalSyntax.defaultPolicy u g
      have ha : assignment OrdinalSyntax.defaultPolicy (.app t .zeroC) = some a := by
        change (assignment OrdinalSyntax.defaultPolicy t).bind
          (fun vf => some (application OrdinalSyntax.defaultPolicy vf g)) = some a
        rw [hu]
        rfl
      obtain ⟨v,hv,he⟩ := saturate_assignment r (.app t .zeroC) a ha
      refine ⟨v,hv,?_⟩
      intro ν
      rw [he ν]
      exact AbsoluteObserver.Proof.ground_application_positive ν u g (headIndex r) (by change 0 < 1; decide)
termination_by r

theorem saturation : Targets.Saturation := by
  intro Γ r t
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ _ OrdinalSyntax.defaultPolicy t
  obtain ⟨v,hv,he⟩ := saturate_assignment r t u hu
  exact ⟨u,v,hu,hv,he⟩

theorem value_support_congr {Γ : List Ty} (t : OrdinalExpression Γ)
    (ν μ : OrdinalComponent Γ → Ordinal)
    (h : ∀ c ∈ ordinalExpressionVariables t, ν c = μ c) : denote ν t = denote μ t := by
  induction t with
  | var c => exact h c (by simp [ordinalExpressionVariables])
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
      simp only [denote]
      rw [iha (fun c hc => h c (List.mem_append_left _ hc)),
        ihb (fun c hc => h c (List.mem_append_right _ hc))]

theorem positive_unit_value {Γ : List Ty} (i : Nat) (t : OrdinalExpression Γ)
    (hi : 0 < i) (hg : GeneratedOrdinalGrade Γ i t) (ρ : Variable Γ .ground → Nat) :
    expressionValue (UnitObservation.substitution ρ) t = denote (fun _ => 1) t := by
  apply value_support_congr
  intro c hc
  have hj := actualGeneratedComponentIndex Γ i t hg c hc
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground =>
      change i ≤ j.val at hj
      have hlt : j.val < 1 := j.isLt
      omega
  | arrow a b => rfl

theorem ground_close_value {Γ : List Ty} (t : OrdinalExpression Γ)
    (ρ : Variable Γ .ground → Nat) :
    expressionValue (UnitObservation.substitution ρ) (GroundClosing.expression (groundMap Γ) t) =
      denote (fun _ => 1) t := by
  induction t with
  | var c =>
      rcases c with ⟨σ,x,j⟩
      cases σ <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
      simp only [GroundClosing.expression,substitute,expressionValue,denote] at *
      rw [iha,ihb]

theorem captureClosing : Targets.CaptureClosing := by
  intro Γ τ t
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  let v := GroundClosing.vector (groundMap Γ) u
  have hv : assignment OrdinalSyntax.defaultPolicy (closeGround t) = some v := by
    rw [closeGround,GroundClosing.StatementChecks.assignmentNaturality,hu]
    rfl
  refine ⟨u,v,hu,hv,rfl,?_⟩
  intro ρ μ j hj
  exact (ground_close_value (u j) μ).trans (positive_unit_value j.val (u j) hj (hg j) ρ).symm

/-- Actual source free-occurrence support, including arbitrary internal binders. -/
theorem closeGround_no_ground {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ)
    (x : Variable Γ .ground) :
    ⟨.ground,x⟩ ∉ SourceFreeOccurrences.freeOccurrences (closeGround t) := by
  rw [closeGround,SourceFreeOccurrencesProof.exactFreeOccurrenceSubstitution]
  simp only [List.mem_flatMap]
  rintro ⟨⟨σ,y⟩,hy,hx⟩
  cases σ <;> simp [groundMap,GroundClosing.GroundMap.source,GroundClosing.Image.source,
    SourceFreeOccurrences.freeOccurrences] at hx

theorem carrier_no_ground {Γ : List Ty} {k r : Nat}
    (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)))
    (x : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground) :
    ⟨.ground,x⟩ ∉ SourceFreeOccurrences.freeOccurrences (carrier t) :=
  closeGround_no_ground _ x

theorem actualCarrier : Targets.ActualCarrier := by
  intro Γ k r t
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated _ _ OrdinalSyntax.defaultPolicy t
  let ur := SourceRenaming.renameVector renameTracked u
  have hur : assignment OrdinalSyntax.defaultPolicy (t.rename renameTracked) = some ur := by
    rw [SourceRenaming.Proof.assignmentNaturality,hu]
    rfl
  obtain ⟨w,hw,he⟩ := saturate_assignment r (t.rename renameTracked) ur hur
  let v := GroundClosing.vector (groundMap _) w
  have hv : assignment OrdinalSyntax.defaultPolicy (carrier t) = some v := by
    rw [carrier,closeGround,GroundClosing.StatementChecks.assignmentNaturality,hw]
    rfl
  refine ⟨u,w,v,hu,hw,hv,rfl,rfl,?_⟩
  intro ρ μ
  change expressionValue (UnitObservation.substitution μ)
    (GroundClosing.expression (groundMap _) (w 1)) = _
  rw [ground_close_value,he (fun _ => 1)]
  change denote (fun _ => 1) (ordinalExpressionRename renameTracked (u (headIndex r))) = _
  rw [AbsoluteObserver.Proof.rename_value]
  exact (positive_unit_value 1 (u (headIndex r)) (by decide) (hg (headIndex r)) ρ).symm
end LogicLineages.OrdinalComparison.Source.UnaryCarrier.Proof
