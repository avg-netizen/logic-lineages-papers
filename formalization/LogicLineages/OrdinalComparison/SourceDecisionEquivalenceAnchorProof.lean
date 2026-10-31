module
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceTargets
public import LogicLineages.OrdinalComparison.SourceObserverPlanProof
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
open GroundEquivalence PrimitiveLowering OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem anchor_value {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v) :
    denote (fun _ => 1) (v 0)=(AbsoluteObserver.anchor hΓ t : Ordinal) := by
  obtain ⟨w,s,hw,_,_,_,_,_,hvalue⟩ := AbsoluteObserver.Proof.anchorCorrect Γ hΓ τ t
  have hc := GroundClosing.Proof.assignmentNaturality Γ [] τ (AbsoluteObserver.closingMap hΓ)
    OrdinalSyntax.defaultPolicy t
  rw [hv] at hc
  change AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (AbsoluteObserver.close hΓ t)=
    some (GroundClosing.vector (AbsoluteObserver.closingMap hΓ) v) at hc
  have he := Option.some.inj (hw.symm.trans hc)
  have hh := hvalue (fun _ => 1)
  rw [he] at hh
  change denote (fun _ => 1) (GroundClosing.expression (AbsoluteObserver.closingMap hΓ) (v 0))=_ at hh
  rw [AbsoluteObserver.Proof.closing_value] at hh
  exact hh

theorem anchor_rename {Γ Δ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (hΔ : ∀ σ ∈ Δ, σ=Ty.ground) (r : Renaming Γ Δ) (t : OriginalTerm Γ τ) :
    AbsoluteObserver.anchor hΔ (t.rename r)=AbsoluteObserver.anchor hΓ t := by
  obtain ⟨v,hv,_,_⟩ := GroundPositiveQuerySplit.Proof.actualScalar Γ hΓ τ t (fun _ => 0)
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r)=
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ τ r OrdinalSyntax.defaultPolicy t,hv]
    rfl
  have hs := anchor_value hΔ (t.rename r) (SourceRenaming.renameVector r v) hr
  change denote (fun _ => 1) (ordinalExpressionRename r (v 0))=_ at hs
  rw [AbsoluteObserver.Proof.rename_value] at hs
  exact Nat.cast_injective (hs.symm.trans (anchor_value hΓ t v hv))

theorem scalar_rename {Γ Δ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (hΔ : ∀ σ ∈ Δ, σ=Ty.ground) (r : Renaming Γ Δ) (t : OriginalTerm Γ τ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat) (h : ∀ x, ν (r x)=ρ x) :
    GroundPositiveQuerySplit.scalarValue (ExistentialPlan.inputs ν) (t.rename r)=
      GroundPositiveQuerySplit.scalarValue (ExistentialPlan.inputs ρ) t := by
  obtain ⟨v,hv,hvs,_⟩ := GroundPositiveQuerySplit.Proof.actualScalar Γ hΓ τ t (ExistentialPlan.inputs ρ)
  obtain ⟨w,hw,hws,_⟩ := GroundPositiveQuerySplit.Proof.actualScalar Δ hΔ τ (t.rename r) (ExistentialPlan.inputs ν)
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r)=
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ τ r OrdinalSyntax.defaultPolicy t,hv]
    rfl
  have he := Option.some.inj (hw.symm.trans hr)
  rw [he] at hws
  rw [← ExistentialPlan.Proof.valuation_inputs] at hvs hws
  change denote (valuation (UnitObservation.substitution ν)) (ordinalExpressionRename r (v 0))=_ at hws
  rw [AbsoluteObserver.Proof.rename_value,ExistentialPlan.Proof.valuation_rename r ρ ν h] at hws
  exact Nat.cast_injective (hws.symm.trans hvs)

theorem template_scalar (Γ : List Ty) (τ : Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (t : Input Γ τ) (v : Port Γ) (C : Nat) (ρ : Variable Γ .ground → Nat)
    (hc : C=AbsoluteObserver.anchor hΓ t.term) :
    ExistentialPlan.Eval ρ (ObserverPlan.template hΓ t v C) ↔
      v.value (ExistentialPlan.inputs ρ)=GroundPositiveQuerySplit.scalarValue (ExistentialPlan.inputs ρ) t.term := by
  have he : ObserverPlan.template hΓ t v C=ObserverPlan.realize hΓ t v := by
    unfold ObserverPlan.realize
    rw [(ObserverPlan.Proof.effectiveAnchor.2 Γ τ hΓ t).1, hc]
  rw [he,ObserverPlan.Proof.observerExact]
  obtain ⟨w,hw,hws,_⟩ := GroundPositiveQuerySplit.Proof.actualScalar Γ hΓ τ t.term (ExistentialPlan.inputs ρ)
  rw [← ExistentialPlan.Proof.valuation_inputs] at hws
  constructor
  · rintro ⟨z,hz,hzs⟩
    rw [hw] at hz
    cases Option.some.inj hz
    exact Nat.cast_injective (hzs.symm.trans hws)
  · intro hv
    refine ⟨w,hw,?_⟩
    rw [hv]
    exact hws
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
