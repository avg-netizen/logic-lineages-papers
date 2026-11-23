module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalNeutralTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowExternalNeutralTargets

theorem nonLambda : PrimaryPreservesNonLambda := by
  intro S K C τ q r h
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | refl _ => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ hq hr => exact hq.trans hr
  | lam _ _ =>
    constructor <;> intro h σ body e <;> exact (h _ _ rfl).elim
  | _ =>
    first
    | exact True.intro
    | constructor <;> intro h σ body e <;> cases e

private def AppComponents (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (before after : NTerm) : Prop :=
  ∀ σ τ q u, before = .auxApp σ τ q u →
    ∃ r v, after = .auxApp σ τ r v ∧ Primary S K C (.arrow σ τ) q r ∧ Primary S K C σ u v

private theorem appComponentsTrans {S K C q r t}
    (hqr : AppComponents S K C q r) (hrt : AppComponents S K C r t) : AppComponents S K C q t := by
  intro σ τ f a hq
  obtain ⟨g, b, hr, hfg, hab⟩ := hqr σ τ f a hq
  obtain ⟨j, c, ht, hgj, hbc⟩ := hrt σ τ g b hr
  exact ⟨j, c, ht, .trans hfg hgj, .trans hab hbc⟩

private theorem appComponentsBoth {S K C τ q r} (h : Primary S K C τ q r) :
    AppComponents S K C q r ∧ AppComponents S K C r q := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | refl ht =>
    constructor <;> intro σ τ f a e <;> cases e <;> cases ht <;>
      refine ⟨_, _, rfl, .refl ?_, .refl ?_⟩ <;> assumption
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ hq hr => exact ⟨appComponentsTrans hq.1 hr.1, appComponentsTrans hr.2 hq.2⟩
  | appFunction hf ha _ =>
    constructor
    · intro σ τ f a h
      cases h
      exact ⟨_, _, rfl, hf, .refl ha⟩
    · intro σ τ f a h
      cases h
      exact ⟨_, _, rfl, .symm hf, .refl ha⟩
  | appArgument hf ha _ =>
    constructor
    · intro σ τ f a h
      cases h
      exact ⟨_, _, rfl, .refl hf, ha⟩
    · intro σ τ f a h
      cases h
      exact ⟨_, _, rfl, .refl hf, .symm ha⟩
  | _ =>
    first
    | exact True.intro
    | constructor <;> intro σ τ f a h <;> cases h

theorem applicationComponents : PrimaryAuxApplicationComponents := by
  intro S K C σ τ q u out h
  exact (appComponentsBoth h).1 σ τ q u rfl

/-- Class equality reflects the original equivalence, at any typed context. -/
theorem primaryOfClassEquality {S K C τ} (q r : WindowCarrier S K C τ)
    (h : classOf q = classOf r) : Primary S K C τ q.val r.val := by
  let presentation : Setoid (WindowCarrier S K C τ) :=
    ⟨fun x y => Primary S K C τ x.val y.val,
      ⟨fun x => .refl x.property.1, fun h => .symm h, fun h e => .trans h e⟩⟩
  change Quotient.mk presentation q = Quotient.mk presentation r at h
  exact Quotient.exact h

theorem representatives : ExactNonLambdaRepresentatives := by
  intro S K C τ q
  constructor
  · intro h
    exact h q rfl
  · intro h r hr
    exact (nonLambda S K C τ q.val r.val (primaryOfClassEquality q r hr.symm)).mp h

end LogicLineages.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
