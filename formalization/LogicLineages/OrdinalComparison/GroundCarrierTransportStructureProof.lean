module
public import LogicLineages.OrdinalComparison.GroundCarrierTransportTargets
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingAlgebraProof
public import LogicLineages.OrdinalComparison.WWGroundClosingPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
open GroundClosing ScalarCarrierAccounting ActiveScalarAnnotation HeadFiniteSurplus
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem exactUnitValue : Targets.ExactUnitValue := by
  intro Γ Δ r q
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases hx : r x <;> simp [unitValue, expression, substitute, component, hx, denote]
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [unitValue, expression, substitute, denote] at iha ihb ⊢
    rw [iha,ihb]

theorem active_map {k Γ Δ} (r : GroundMap Γ Δ)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Δ) _) (expression r.lift q) ↔
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q := by
  constructor
  · intro ha
    by_contra hn
    have hf := HeadFiniteSurplus.Proof.headFree_of_inactive q hn
    have hf' : ordinalHeadFree (expression r.lift q) = true :=
      (GroundClosing.Proof.head_free r q).trans hf
    exact ScalarCarrierAccounting.Proof.inactive_of_headFree _ hf' ha
  · intro ha
    by_contra hn
    have hf := HeadFiniteSurplus.Proof.headFree_of_inactive (expression r.lift q) hn
    rw [GroundClosing.Proof.head_free] at hf
    exact ScalarCarrierAccounting.Proof.inactive_of_headFree q hf ha

theorem surplus_map {k Γ Δ} (r : GroundMap Γ Δ)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) :
    surplus (expression r.lift q) = surplus q := by
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => rfl
    | there x =>
      cases hx : r x <;>
        simp [expression, substitute, component, GroundMap.lift, Image.weaken, hx,
          surplus, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
  | zero | one | omega => rfl
  | add a b iha ihb =>
    change (if ordinalHeadFree (expression r.lift (.add a b)) then 1
      else surplus (expression r.lift a) + surplus (expression r.lift b) + 1) =
        (if ordinalHeadFree (.add a b) then 1 else surplus a + surplus b + 1)
    rw [GroundClosing.Proof.head_free, iha, ihb]
  | emul a b iha ihb =>
    change (if ordinalHeadFree (expression r.lift (.emul a b)) then 1 else 0) =
      (if ordinalHeadFree (.emul a b) then 1 else 0)
    rw [GroundClosing.Proof.head_free]
  | collapse a b iha ihb =>
    change (if ordinalHeadFree (expression r.lift (.collapse a b)) then 1 else 0) =
      (if ordinalHeadFree (.collapse a b) then 1 else 0)
    rw [GroundClosing.Proof.head_free]

theorem trackedInvariants : Targets.TrackedInvariants := by
  intro k Γ Δ r q
  exact ⟨GroundClosing.Proof.head_free r q, active_map r q, surplus_map r q⟩

end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
