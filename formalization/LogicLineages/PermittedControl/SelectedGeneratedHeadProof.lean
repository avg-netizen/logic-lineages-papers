module
public import LogicLineages.PermittedControl.SelectedCanonicalDomainTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedHeadProof
open OrdinalComparison Source SelectedSourceDomain

theorem freeAmbientHead (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (h : AmbientGrade ctrl (σ :: Γ) i t) :
    ordinalHeadFree t = true → HeadGrade ctrl Γ σ i t := by
  induction h with
  | one i => intro _; exact .one i
  | omega i hi => intro _; exact .omega i hi
  | var x j => intro _; exact .var x j
  | @add i f g hf hg ihf ihg =>
    intro hfree
    have hparts : ordinalHeadFree f = true ∧ ordinalHeadFree g = true := by
      simpa [ordinalHeadFree, ordinalHeadOccurs] using hfree
    exact .add (ihf hparts.1) (ihg hparts.2)
  | @emul i f g hi hf hg ihf ihg =>
    intro hfree
    have hparts : ordinalHeadFree f = true ∧ ordinalHeadFree g = true := by
      simpa [ordinalHeadFree, ordinalHeadOccurs] using hfree
    exact .emul hi (ihf hparts.1) (ihg hparts.2)
  | @collapse f g hf hg hn ihf ihg =>
    intro hfree
    have hparts : ordinalHeadFree f = true ∧ ordinalHeadFree g = true := by
      simpa [ordinalHeadFree, ordinalHeadOccurs] using hfree
    exact .collapse (ihf hparts.1) (ihg hparts.2) hn
  | promote hi hh ih =>
    intro hfree
    exact .promote hi (ih hfree) hfree

private def scalarShape (ctrl : Nat → Nat) {Γ : List Ty} : OrdinalExpression Γ → Prop
  | .one => True
  | .var c => c.2.2.val = 0
  | .add f g => AmbientGrade ctrl Γ 0 f ∧ AmbientGrade ctrl Γ 0 g
  | .collapse _ _ => True
  | _ => False

private theorem scalar_shape {ctrl : Nat → Nat} {Γ : List Ty} {i : Nat} {t : OrdinalExpression Γ}
    (h : AmbientGrade ctrl Γ i t) : i = 0 → scalarShape ctrl t := by
  induction h with
  | one i => intro _; trivial
  | omega i hi => intro he; omega
  | var x j => intro he; exact he
  | add hf hg ihf ihg => intro he; subst he; exact ⟨hf, hg⟩
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg hn ihf ihg => intro _; trivial
  | promote hi hh ih => intro he; omega

private theorem generated_positive_scalar_free {ctrl : Nat → Nat} {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (hg : GeneratedOrdinalGrade (σ :: Γ) i t) :
    0 < i → AmbientGrade ctrl (σ :: Γ) 0 t → ordinalHeadFree t = true := by
  induction hg with
  | one i => intro _ _; rfl
  | omega i hi => intro _ hs; exact False.elim (scalar_shape hs rfl)
  | var x j => intro hi hs; have hz := scalar_shape hs rfl; change j.val = 0 at hz; omega
  | add hf hg ihf ihg =>
    intro hi hs
    have hp := scalar_shape hs rfl
    have hff := ihf hi hp.1
    have hgf := ihg hi hp.2
    simp [ordinalHeadFree, ordinalHeadOccurs] at hff hgf ⊢
    exact ⟨hff, hgf⟩
  | emul hi hf hg ihf ihg => intro _ hs; exact False.elim (scalar_shape hs rfl)
  | collapse hf hg ihf ihg => intro hi _; omega

private theorem generated_collapse_parts {Γ : List Ty} {i : Nat} {t : OrdinalExpression Γ}
    (h : GeneratedOrdinalGrade Γ i t) :
    (match t with
      | .collapse f g => GeneratedOrdinalGrade Γ 1 f ∧ GeneratedOrdinalGrade Γ 0 g
      | _ => True) := by
  cases h <;> simp_all

theorem generatedAmbientHead : SelectedCanonicalDomainTargets.GeneratedAmbientHead := by
  intro ctrl Γ σ i t hg ha
  induction ha with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j => exact .var x j
  | add hf hh ihf ihh =>
    cases hg with
    | add gf gh => exact .add (ihf gf) (ihh gh)
  | emul hi hf hh ihf ihh =>
    cases hg with
    | emul hgi gf gh => exact .emul hi (ihf gf) (ihh gh)
  | collapse hf hh hn ihf ihh =>
    have hp := generated_collapse_parts hg
    exact .collapse (ihf hp.1) (ihh hp.2) hn
  | promote hi hh ih =>
    have hfree := generated_positive_scalar_free hg hi hh
    exact .promote hi (freeAmbientHead ctrl Γ σ 0 _ hh hfree) hfree

end LogicLineages.PermittedControl.SelectedGeneratedHeadProof
