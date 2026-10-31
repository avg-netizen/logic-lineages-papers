module
public import LogicLineages.OrdinalComparison.WWOriginalDomainTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem originalFiniteValueCalibration : Targets.OriginalFiniteValueCalibration := by
  intro n
  simp [finiteValue, Ordinal.card_nat]

private theorem closed_scalar_finite {i : Nat} {t : ClosedExpression}
    (h : ClosedGrade i t) : i = 0 → ∃ n : Nat, closedValue t = (n : Ordinal) := by
  induction h with
  | one i => intro _; exact ⟨1, by simp [closedValue, expressionValue, denote]⟩
  | omega i hi => intro he; omega
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a, ha⟩ := ihf he
    obtain ⟨b, hb⟩ := ihg he
    refine ⟨a + b, ?_⟩
    change ordinalNaturalSum (closedValue _) (closedValue _) = _
    rw [ha, hb, naturalSum_finite]
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg hn ihf ihg => intro _; exact ⟨_, rfl⟩
  | promote hi hh ih => intro he; omega

theorem originalClosedScalarFinite : Targets.OriginalClosedScalarFinite :=
  fun _ h => closed_scalar_finite h rfl

private theorem ambient_scalar_finite {Γ : List Ty} {i : Nat} {t : OrdinalExpression Γ}
    (h : AmbientGrade Γ i t) (ρ : AdmissibleSubstitution Γ) :
    i = 0 → ∃ n : Nat, expressionValue ρ t = (n : Ordinal) := by
  induction h with
  | one i => intro _; exact ⟨1, by simp [closedValue, expressionValue, denote]⟩
  | omega i hi => intro he; omega
  | var x j =>
    intro he
    have hj : j = 0 := Fin.ext he
    subst j
    exact originalClosedScalarFinite _ (ρ.graded x 0)
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a, ha⟩ := ihf he
    obtain ⟨b, hb⟩ := ihg he
    refine ⟨a + b, ?_⟩
    change ordinalNaturalSum (expressionValue ρ _) (expressionValue ρ _) = _
    rw [ha, hb, naturalSum_finite]
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg hn ihf ihg => intro _; exact ⟨_, rfl⟩
  | promote hi hh ih => intro he; omega

theorem originalAmbientScalarFinite : Targets.OriginalAmbientScalarFinite :=
  fun _ _ h ρ => ambient_scalar_finite h ρ rfl

theorem originalAllOneSubstitution : Targets.OriginalAllOneSubstitution := by
  intro Γ
  refine ⟨⟨(fun {_} _ _ => .one), (fun {_} _ j => .one j.val),
    (fun {_} _ _ => le_rfl)⟩, ?_⟩
  intro τ x j
  rfl

theorem originalHeadOneExtension : Targets.OriginalHeadOneExtension := by
  intro Γ σ ρ
  let v : {τ : Ty} → Variable (σ :: Γ) τ → Fin (τ.level + 1) → ClosedExpression :=
    fun {_} x j => match x with
      | .here => .one
      | .there y => ρ.vector y j
  have hg : ∀ {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)),
      ClosedGrade j.val (v x j) := by
    intro τ x j
    cases x with
    | here => exact .one j.val
    | there y => exact ρ.graded y j
  have hb : ∀ {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)),
      actualOrdinalNorm (closedValue (v x j)) ≤ actualOrdinalNorm (closedValue (v x 0)) := by
    intro τ x j
    cases x with
    | here => exact le_rfl
    | there y => exact ρ.bounded y j
  refine ⟨⟨v, hg, hb⟩, ?_, ?_⟩
  · intro j; rfl
  · intro τ x j; rfl

theorem originalHeadAmbientInclusion : Targets.OriginalHeadAmbientInclusion := by
  intro Γ σ i t h
  induction h with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j => exact .var x j
  | add hf hg ihf ihg => exact .add ihf ihg
  | emul hi hf hg ihf ihg => exact .emul hi ihf ihg
  | collapse hf hg hn ihf ihg => exact .collapse ihf ihg hn
  | promote hi hh hfree ih => exact .promote hi ih

theorem originalHeadLiteralAdmission : Targets.OriginalHeadLiteralAdmission := by
  intro Γ σ i t h
  induction h with
  | one i => exact .free i .one rfl
  | omega i hi => exact .free i .omega rfl
  | var x j =>
    cases x with
    | here => exact .tracked j
    | there y => exact .free j.val _ rfl
  | add hf hg ihf ihg => exact .add ihf ihg
  | emul hi hf hg ihf ihg => exact .emul hi ihf ihg
  | collapse hf hg hn ihf ihg => exact .collapse ihf ihg
  | promote hi hh hfree ih => exact .free _ _ hfree

end LogicLineages.OrdinalComparison.Source.OriginalDomain
