module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveOriginProof
public import LogicLineages.OrdinalComparison.WWGroundClosingStatementChecks
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation GroundClosing HeadFiniteSurplus
open CurrentUnaryChain (commonUnits)
open ParametricSourceSuccessor

theorem trackedActiveMap {k Γ Δ} (r : GroundMap Γ Δ)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Δ) _) (expression r.lift q) ↔
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q := by
  constructor
  · intro ha
    by_contra hn
    have hf := HeadFiniteSurplus.Proof.headFree_of_inactive q hn
    have hf' : ordinalHeadFree (expression r.lift q) = true :=
      (GroundClosing.Proof.head_free r q).trans hf
    exact inactiveOfHeadFree _ hf' ha
  · intro ha
    by_contra hn
    have hf := HeadFiniteSurplus.Proof.headFree_of_inactive (expression r.lift q) hn
    rw [GroundClosing.Proof.head_free] at hf
    exact inactiveOfHeadFree q hf ha

theorem surplusMap {k Γ Δ} (r : GroundMap Γ Δ)
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

def pullGround {Γ Δ : List Ty} (r : GroundMap Γ Δ)
    (ν : Variable Δ .ground → Nat) (x : Variable Γ .ground) : Nat :=
  match r x with
  | .var y => ν y
  | .zero => 0

/-- Semantic substitution for the same f. The actual literal source zero
denotes one under the encoded ground-zero valuation; kept names are read
at their real new wire, and old functional names remain common units. -/
theorem groundValue (f : Nat → Nat) {Γ Δ : List Ty} (r : GroundMap Γ Δ)
    (ν : Variable Δ .ground → Nat) (q : OrdinalExpression Γ) :
    denoteWith f (commonUnits ν) (GroundClosing.expression r q) =
      denoteWith f (commonUnits (pullGround r ν)) q := by
  unfold GroundClosing.expression
  rw [ParametricSourceSuccessor.Proof.exactSubstitution]
  congr 1
  funext c
  rcases c with ⟨τ,x,j⟩
  cases τ with
  | ground =>
    cases hr : r x with
    | var y => simp [component,hr,denoteWith,commonUnits,pullGround]
    | zero => simp [component,hr,denoteWith,commonUnits,pullGround]
  | arrow a b =>
    cases hr : r x with
    | var y => simp [component,hr,denoteWith,commonUnits]

theorem exactUnitMap (f : Nat → Nat) {Γ Δ : List Ty} (r : GroundMap Γ Δ) (q : OrdinalExpression Γ) :
    unitValue f (GroundClosing.expression r q) = unitValue f q := by
  unfold unitValue
  rw [groundValue]
  have h : pullGround r (fun _ => 0) = fun _ => 0 := by
    funext x
    unfold pullGround
    cases r x <;> rfl
  rw [h]

theorem groundUnitAccountTransport : CurrentReserveTargets.GroundUnitAccountTransport := by
  intro p f k Γ Δ r q xs c hq
  induction hq with
  | free hn => exact .free (fun h => hn ((trackedActiveMap r _).mp h))
  | tracked => exact .tracked
  | add ha _ _ iha ihb => exact .add ((trackedActiveMap r _).mpr ha) iha ihb
  | @finite h t xs c n ha hn _ ih =>
    rw [← surplusMap r h]
    exact .finite ((trackedActiveMap r _).mpr ha) ((exactUnitMap f r.lift h).trans hn) ih
  | @nonfinite h t xs c a ha hn he _ _ ih =>
    rw [← surplusMap r h]
    have hU := exactUnitMap f r.lift h
    exact .nonfinite a ((trackedActiveMap r _).mpr ha) (hU.symm ▸ hn)
      (he.trans hU.symm) (fun h => by cases h) ih

theorem actualGroundUnitTransport : CurrentReserveTargets.ActualGroundUnitTransport := by
  intro p f k Γ Δ n r e
  obtain ⟨u,hu,ht,ha⟩ := originalCertificates p k (Ty.curriedGround (k+1) :: Γ) .here n e
  obtain ⟨xs,c,v,hspawn,haccount,hv,hvalue⟩ := exactAnnotatedAccounting p f k Γ _ ht ha
  let w := GroundClosing.partialVector r v
  have hclosed : AdmissibleAssignment.assignment p
      (GroundCarrierTransport.close r (TrackedSource.erase e)) = some (GroundClosing.vector r.lift u) := by
    rw [GroundCarrierTransport.close,GroundClosing.StatementChecks.assignmentNaturality,hu] <;> rfl
  have hw : AdmissiblePartial.run p 0 (GroundClosing.expression r.lift (u 0)) = some w := by
    rw [GroundClosing.StatementChecks.partialNaturality,hv] <;> rfl
  refine ⟨u,xs,c,v,w,hu,hspawn,haccount,hv,hclosed,
    groundUnitAccountTransport p f k Γ Δ r (u 0) xs c haccount,hw,rfl,?_⟩
  intro μ ν
  refine ⟨hvalue μ,?_⟩
  change denoteWith f (commonUnits ν) (GroundClosing.expression r (v (outputOne k))) = _
  rw [groundValue]
  exact hvalue (pullGround r ν)

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
