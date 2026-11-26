module
public import LogicLineages.PermittedControl.LiteralCovarianceTargets
@[expose] public section
namespace LogicLineages.PermittedControl.LiteralCovarianceProof
open OrdinalComparison Source Source.AdmissibleSum LiteralCovariance
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def mapPartial {Γ Δ : List Ty} {σ : Ty} (r : TailSubstitution Γ Δ)
    (v : OrdinalPartialVector Γ σ) : OrdinalPartialVector Δ σ := fun j => apply r (v j)

@[simp] theorem subst_one {Γ Δ} (r : TailSubstitution Γ Δ) :
    apply r .one = .one := rfl
@[simp] theorem subst_add {Γ Δ} (r : TailSubstitution Γ Δ) (a b : OrdinalExpression Γ) :
    apply r (.add a b) =
      .add (apply r a) (apply r b) := rfl
@[simp] theorem subst_emul {Γ Δ} (r : TailSubstitution Γ Δ) (a b : OrdinalExpression Γ) :
    apply r (.emul a b) =
      .emul (apply r a) (apply r b) := rfl
@[simp] theorem subst_collapse {Γ Δ} (r : TailSubstitution Γ Δ) (a b : OrdinalExpression Γ) :
    apply r (.collapse a b) =
      .collapse (apply r a) (apply r b) := rfl

theorem subst_expand {Γ Δ} (r : TailSubstitution Γ Δ) {n : Nat}
    (s : AdmissibleSum.Shape n) (xs : Fin n → OrdinalExpression Γ) :
    apply r (AdmissibleSum.expand s xs) =
      AdmissibleSum.expand s (fun j => apply r (xs j)) := by
  induction s with
  | leaf => rfl
  | join a b iha ihb => simp only [AdmissibleSum.expand, subst_add, iha, ihb]

theorem subst_three {Γ Δ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    (site : AdmissibleSum.MacroSite) (a b c : OrdinalExpression Γ) :
    apply r (AdmissiblePartial.three p site a b c) =
      AdmissiblePartial.three p site (apply r a)
        (apply r b) (apply r c) := by
  unfold AdmissiblePartial.three
  rw [subst_expand]
  congr 1
  funext j
  split_ifs <;> rfl

theorem subst_twice {Γ Δ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    (a : OrdinalExpression Γ) :
    apply r (AdmissiblePartial.twice p a) =
      AdmissiblePartial.twice p (apply r a) := by
  exact subst_expand r _ _

theorem weaken_occurs {Γ} (σ : Ty) (t : OrdinalExpression Γ) :
    ordinalHeadOccurs (weaken σ t) = false := by
  induction t with
  | var c => rcases c with ⟨τ,v,j⟩; rfl
  | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp only [weaken, ordinalExpressionRename, substitute, ordinalHeadOccurs] at *
    rw [ha,hb]
    rfl

theorem weaken_closure {Γ} (σ : Ty) (t : OrdinalExpression Γ) :
    ordinalHeadClosure (weaken σ t) = t := by
  induction t with
  | var c => rcases c with ⟨τ,v,j⟩; rfl
  | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp_all only [weaken, ordinalExpressionRename, substitute, ordinalHeadClosure]

theorem head_occurs {Γ Δ σ} (r : TailSubstitution Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadOccurs (apply (lift σ r) t) = ordinalHeadOccurs t := by
  induction t with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => rfl
    | there v => exact weaken_occurs σ (r ⟨τ,v,j⟩)
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    simp only [apply, substitute, ordinalHeadOccurs] at *
    rw [ihf, ihg]

theorem head_free {Γ Δ σ} (r : TailSubstitution Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadFree (apply (lift σ r) t) = ordinalHeadFree t := by
  simp only [ordinalHeadFree, head_occurs]

theorem partial_size {Γ Δ σ} (r : TailSubstitution Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalPartialSize (apply (lift σ r) t) = ordinalPartialSize t := by
  induction t with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => rfl
    | there v =>
      change ordinalPartialSize (weaken σ (r ⟨τ,v,j⟩)) = 1
      rw [ordinalPartialSize.eq_def]
      simp only [ordinalHeadFree, weaken_occurs, Bool.not_false, ↓reduceIte]
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    conv_lhs => rw [ordinalPartialSize.eq_def]
    conv_rhs => rw [ordinalPartialSize.eq_def]
    rw [head_free]
    split <;> simp_all only [apply, substitute]

theorem head_closure {Γ Δ σ} (r : TailSubstitution Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadClosure (apply (lift σ r) t) =
      apply r (ordinalHeadClosure t) := by
  induction t with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => rfl
    | there v => exact weaken_closure σ (r ⟨τ,v,j⟩)
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    simp_all only [ordinalHeadClosure, apply, substitute]

theorem free_partial {Γ Δ σ} (r : TailSubstitution Γ Δ) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) :
    ordinalFreePartialVector i (apply (lift σ r) t) =
      mapPartial r (ordinalFreePartialVector i t) := by
  funext j
  simp only [ordinalFreePartialVector, mapPartial, head_closure]
  split_ifs <;> simp

theorem run_free {Γ Δ σ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    (i : Nat) (t : OrdinalExpression (σ :: Γ)) (ht : ordinalHeadFree t = true) :
    AdmissiblePartial.run p i (apply (lift σ r) t) =
      (AdmissiblePartial.run p i t).map (mapPartial r) := by
  conv_lhs => rw [AdmissiblePartial.run.eq_def]
  conv_rhs => rw [AdmissiblePartial.run.eq_def]
  simp only [head_free, ht, ↓reduceIte, Option.map_some]
  exact congrArg some (free_partial r i t)

theorem partialNaturality : LiteralCovarianceTargets.PartialCovariance := by
  intro Γ Δ σ r p i t
  induction t generalizing i with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here =>
      simp [AdmissiblePartial.run, apply, substitute,
        lift, ordinalHeadFree, ordinalHeadOccurs,
        ordinalHeadComponentOccurs, mapPartial]
    | there x => exact run_free r p i (.var ⟨τ, .there x, j⟩) rfl
  | zero => exact run_free r p i .zero rfl
  | one => exact run_free r p i .one rfl
  | omega => exact run_free r p i .omega rfl
  | add f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.add f g) with
    | true => simpa [hh,mapPartial] using congrArg some (free_partial r i (.add f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, subst_add]
      rw [ihf, ihg]
      cases hf : AdmissiblePartial.run p i f <;> cases hg : AdmissiblePartial.run p i g <;>
        simp [hf, hg, mapPartial, subst_three]
  | emul f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.emul f g) with
    | true => simpa [hh,mapPartial] using congrArg some (free_partial r i (.emul f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, subst_emul]
      by_cases hi : 0 < i
      · simp only [hi, ↓reduceIte]
        rw [ihf, ihg]
        cases hf : AdmissiblePartial.run p (i+1) f <;> cases hg : AdmissiblePartial.run p i g <;>
          simp [hf, hg, mapPartial, subst_three, subst_twice]
      · simp [hi]
  | collapse f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.collapse f g) with
    | true => simpa [hh,mapPartial] using congrArg some (free_partial r i (.collapse f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, subst_collapse]
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte]
        rw [ihf, ihg]
        cases hf : AdmissiblePartial.run p 1 f <;> cases hg : AdmissiblePartial.run p 0 g <;>
          simp [hf, hg, mapPartial, head_closure, apply_ite]
      · simp [hi]

end LogicLineages.PermittedControl.LiteralCovarianceProof
