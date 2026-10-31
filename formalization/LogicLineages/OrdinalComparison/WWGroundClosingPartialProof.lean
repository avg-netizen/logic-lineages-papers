module
public import LogicLineages.OrdinalComparison.WWGroundClosingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosing.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

@[simp] theorem rename_one {Γ Δ} (r : GroundMap Γ Δ) :
    expression r .one = .one := rfl
@[simp] theorem rename_add {Γ Δ} (r : GroundMap Γ Δ) (a b : OrdinalExpression Γ) :
    expression r (.add a b) =
      .add (expression r a) (expression r b) := rfl
@[simp] theorem rename_emul {Γ Δ} (r : GroundMap Γ Δ) (a b : OrdinalExpression Γ) :
    expression r (.emul a b) =
      .emul (expression r a) (expression r b) := rfl
@[simp] theorem rename_collapse {Γ Δ} (r : GroundMap Γ Δ) (a b : OrdinalExpression Γ) :
    expression r (.collapse a b) =
      .collapse (expression r a) (expression r b) := rfl

theorem rename_expand {Γ Δ} (r : GroundMap Γ Δ) {n : Nat}
    (s : AdmissibleSum.Shape n) (xs : Fin n → OrdinalExpression Γ) :
    expression r (AdmissibleSum.expand s xs) =
      AdmissibleSum.expand s (fun j => expression r (xs j)) := by
  induction s with
  | leaf => rfl
  | join a b iha ihb => simp only [AdmissibleSum.expand, rename_add, iha, ihb]

theorem rename_three {Γ Δ} (r : GroundMap Γ Δ) (p : AdmissibleSum.Policy)
    (site : AdmissibleSum.MacroSite) (a b c : OrdinalExpression Γ) :
    expression r (AdmissiblePartial.three p site a b c) =
      AdmissiblePartial.three p site (expression r a)
        (expression r b) (expression r c) := by
  unfold AdmissiblePartial.three
  rw [rename_expand]
  congr 1
  funext j
  split_ifs <;> rfl

theorem rename_twice {Γ Δ} (r : GroundMap Γ Δ) (p : AdmissibleSum.Policy)
    (a : OrdinalExpression Γ) :
    expression r (AdmissiblePartial.twice p a) =
      AdmissiblePartial.twice p (expression r a) := by
  exact rename_expand r _ _

theorem head_occurs {Γ Δ σ} (r : GroundMap Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadOccurs (expression r.lift t) = ordinalHeadOccurs t := by
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here => rfl
    | there x => cases h : r x <;> simp [expression, substitute, component, GroundMap.lift, Image.weaken, h, ordinalHeadOccurs, ordinalHeadComponentOccurs, ordinalPartialSize, ordinalHeadFree, ordinalHeadClosure, ordinalHeadClosureComponent]
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    simp only [expression, substitute, ordinalHeadOccurs] at *
    rw [ihf, ihg]

theorem head_free {Γ Δ σ} (r : GroundMap Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadFree (expression r.lift t) = ordinalHeadFree t := by
  simp only [ordinalHeadFree, head_occurs]

theorem partial_size {Γ Δ σ} (r : GroundMap Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalPartialSize (expression r.lift t) = ordinalPartialSize t := by
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here => rfl
    | there x => cases h : r x <;> simp [expression, substitute, component, GroundMap.lift, Image.weaken, h, ordinalHeadOccurs, ordinalHeadComponentOccurs, ordinalPartialSize, ordinalHeadFree, ordinalHeadClosure, ordinalHeadClosureComponent]
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    conv_lhs => rw [ordinalPartialSize.eq_def]
    conv_rhs => rw [ordinalPartialSize.eq_def]
    rw [head_free]
    split <;> simp_all only [expression, substitute]

theorem head_closure {Γ Δ σ} (r : GroundMap Γ Δ) (t : OrdinalExpression (σ :: Γ)) :
    ordinalHeadClosure (expression r.lift t) =
      expression r (ordinalHeadClosure t) := by
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here => rfl
    | there x => cases h : r x <;> simp [expression, substitute, component, GroundMap.lift, Image.weaken, h, ordinalHeadOccurs, ordinalHeadComponentOccurs, ordinalPartialSize, ordinalHeadFree, ordinalHeadClosure, ordinalHeadClosureComponent]
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    simp_all only [ordinalHeadClosure, expression, substitute]

theorem free_partial {Γ Δ σ} (r : GroundMap Γ Δ) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) :
    ordinalFreePartialVector i (expression r.lift t) =
      partialVector r (ordinalFreePartialVector i t) := by
  funext j
  simp only [ordinalFreePartialVector, partialVector, head_closure]
  split_ifs <;> simp

theorem run_free {Γ Δ σ} (r : GroundMap Γ Δ) (p : AdmissibleSum.Policy)
    (i : Nat) (t : OrdinalExpression (σ :: Γ)) (ht : ordinalHeadFree t = true) :
    AdmissiblePartial.run p i (expression r.lift t) =
      (AdmissiblePartial.run p i t).map (partialVector r) := by
  conv_lhs => rw [AdmissiblePartial.run.eq_def]
  conv_rhs => rw [AdmissiblePartial.run.eq_def]
  simp only [head_free, ht, ↓reduceIte, Option.map_some]
  exact congrArg some (free_partial r i t)

theorem partialNaturality : Targets.PartialNaturality := by
  intro Γ Δ σ r p i t
  induction t generalizing i with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x with
    | here =>
      simp [AdmissiblePartial.run, expression, substitute,
        component, GroundMap.lift, component, ordinalHeadFree, ordinalHeadOccurs,
        ordinalHeadComponentOccurs, partialVector]
      split_ifs <;> rfl
    | there x => exact run_free r p i (.var ⟨τ, .there x, j⟩) rfl
  | zero => exact run_free r p i .zero rfl
  | one => exact run_free r p i .one rfl
  | omega => exact run_free r p i .omega rfl
  | add f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.add f g) with
    | true => simpa [hh] using congrArg some (free_partial r i (.add f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, rename_add]
      rw [ihf, ihg]
      cases hf : AdmissiblePartial.run p i f <;> cases hg : AdmissiblePartial.run p i g <;>
        simp [hf, hg, partialVector, rename_three]
      funext j
      simp only [partialVector, rename_three, rename_one]
  | emul f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.emul f g) with
    | true => simpa [hh] using congrArg some (free_partial r i (.emul f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, rename_emul]
      by_cases hi : 0 < i
      · simp only [hi, ↓reduceIte]
        rw [ihf, ihg]
        cases hf : AdmissiblePartial.run p (i+1) f <;> cases hg : AdmissiblePartial.run p i g <;>
          simp [hf, hg, partialVector, rename_three, rename_twice]
        funext j
        simp only [partialVector, rename_three, rename_twice, rename_one]
      · simp [hi]
  | collapse f g ihf ihg =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    rw [head_free]
    cases hh : ordinalHeadFree (.collapse f g) with
    | true => simpa [hh] using congrArg some (free_partial r i (.collapse f g))
    | false =>
      simp only [hh, Bool.false_eq_true, ↓reduceIte, rename_collapse]
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte]
        rw [ihf, ihg]
        cases hf : AdmissiblePartial.run p 1 f <;> cases hg : AdmissiblePartial.run p 0 g <;>
          simp [hf, hg, partialVector, head_closure, apply_ite]
        funext j
        simp only [partialVector]
        split_ifs <;> simp
      · simp [hi]
end LogicLineages.OrdinalComparison.Source.GroundClosing.Proof
