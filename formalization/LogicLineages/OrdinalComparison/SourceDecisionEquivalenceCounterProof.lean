module
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceStructureProof
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceAnchorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
open GroundEquivalence PrimitiveLowering GroundPositiveQuerySplit

theorem template_counter (Γ : List Ty) (τ υ : Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (strict : Bool) (a : Input Γ τ) (b : Input Γ υ) (flag : Bool) (ca cb : Nat)
    (hca : ca=AbsoluteObserver.anchor hΓ a.term) (hcb : cb=AbsoluteObserver.anchor hΓ b.term)
    (ρ : Variable Γ .ground → Nat) :
    ExistentialPlan.Eval ρ (template hΓ strict a b (flag,ca,cb)) ↔
      ¬ (flag=true ∧ (if strict then scalarValue (ExistentialPlan.inputs ρ) a.term<scalarValue (ExistentialPlan.inputs ρ) b.term
        else scalarValue (ExistentialPlan.inputs ρ) a.term≤scalarValue (ExistentialPlan.inputs ρ) b.term)) := by
  cases flag with
  | false => simp only [template,Bool.false_eq_true,if_false,ExistentialPlan.Eval,false_and,not_false_eq_true]
  | true =>
    let Δ := Ty.ground::Ty.ground::Γ
    let r : Renaming Γ Δ := AbsoluteObserver.shiftTwo Γ
    let ar := ScopedDAG.renameInput r a
    let br := ScopedDAG.renameInput r b
    have hac : ca=AbsoluteObserver.anchor (twoGround hΓ) ar.term := by
      rw [(ScopedDAG.Proof.«renaming» Γ Δ τ r a).1]
      exact hca.trans (anchor_rename hΓ (twoGround hΓ) r a.term).symm
    have hbc : cb=AbsoluteObserver.anchor (twoGround hΓ) br.term := by
      rw [(ScopedDAG.Proof.«renaming» Γ Δ υ r b).1]
      exact hcb.trans (anchor_rename hΓ (twoGround hΓ) r b.term).symm
    have hA (na nb : Nat) :
        ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)
          (ObserverPlan.template (twoGround hΓ) ar (.var (.there .here)) ca) ↔
        na=scalarValue (ExistentialPlan.inputs ρ) a.term := by
      have hh := template_scalar Δ τ (twoGround hΓ) ar (.var (.there .here)) ca
        (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb) hac
      change ExistentialPlan.Eval _ _ ↔ na=scalarValue
        (ExistentialPlan.inputs (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)) ar.term at hh
      rw [(ScopedDAG.Proof.«renaming» Γ Δ τ r a).1,
        scalar_rename hΓ (twoGround hΓ) r a.term ρ
          (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb) (fun _ => rfl)] at hh
      exact hh
    have hB (na nb : Nat) :
        ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)
          (ObserverPlan.template (twoGround hΓ) br (.var .here) cb) ↔
        nb=scalarValue (ExistentialPlan.inputs ρ) b.term := by
      have hh := template_scalar Δ υ (twoGround hΓ) br (.var .here) cb
        (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb) hbc
      change ExistentialPlan.Eval _ _ ↔ nb=scalarValue
        (ExistentialPlan.inputs (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)) br.term at hh
      rw [(ScopedDAG.Proof.«renaming» Γ Δ υ r b).1,
        scalar_rename hΓ (twoGround hΓ) r b.term ρ
          (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb) (fun _ => rfl)] at hh
      exact hh
    have hO (na nb : Nat) :
        ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)
          (orderPlan strict (.var (.there .here)) (.var .here)) ↔
        ¬ (if strict then na<nb else na≤nb) :=
      order_correct strict _ _ _
    change (∃ na nb, ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ na) nb)
      (join (ObserverPlan.template (twoGround hΓ) ar (.var (.there .here)) ca)
        (join (ObserverPlan.template (twoGround hΓ) br (.var .here) cb)
          (orderPlan strict (.var (.there .here)) (.var .here))))) ↔ _
    simp only [join_correct,hA,hB,hO,true_and]
    constructor
    · rintro ⟨na,nb,rfl,rfl,hh⟩
      exact hh
    · intro hh
      exact ⟨scalarValue (ExistentialPlan.inputs ρ) a.term,scalarValue (ExistentialPlan.inputs ρ) b.term,rfl,rfl,hh⟩

theorem counter_correct (Γ : List Ty) (τ υ : Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (strict : Bool) (a : Input Γ τ) (b : Input Γ υ) (ρ : Variable Γ .ground → Nat) :
    ExistentialPlan.Eval ρ (realize hΓ strict a b) ↔
      ¬ QueryAt strict a.term b.term (ExistentialPlan.inputs ρ) := by
  have ha := (ObserverPlan.Proof.effectiveAnchor.2 Γ τ hΓ a).1
  have hb := (ObserverPlan.Proof.effectiveAnchor.2 Γ υ hΓ b).1
  have ht := template_counter Γ τ υ hΓ strict a b
    (positiveFlagCode (request a b)) (AbsoluteObserver.openSourceValue (ObserverPlan.request a))
    (AbsoluteObserver.openSourceValue (ObserverPlan.request b)) ha hb ρ
  have hq := GroundPositiveQuerySplit.Proof.querySplit Γ hΓ τ υ a.term b.term (ExistentialPlan.inputs ρ) strict
  exact ht.trans (not_congr hq).symm
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
