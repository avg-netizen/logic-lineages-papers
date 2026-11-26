module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalLambdaEdgesTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambdaShapeProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowPrimary NumberedWindowRules NumberedWindowExternalLambda
open NumberedWindowExternalLambdaEdgesTargets NumberedWindowExternalNeutralPrimaryProof
open NumberedWindowPreservationGuardProof (lamBody)

theorem literal : LambdaClassLiteral := by
  intro S K C σ τ hk hτ v
  exact ⟨rfl,rfl⟩

private def LamView (S : Signature) (K : List Ty) (C : BoundContext) (t : Ty)
    (q r : NTerm) : Prop :=
  ∀ σ τ v, t = .arrow σ τ → q = .lam σ v →
    ∃ w, r = .lam σ w ∧ Primary S K (C.push σ) τ v w

private theorem transView {S K C t q r w} (p : LamView S K C t q r) (h : LamView S K C t r w) :
    LamView S K C t q w := by
  intro σ τ v eq hv
  obtain ⟨u,hr,e⟩ := p σ τ v eq hv
  obtain ⟨b,hw,d⟩ := h σ τ u eq hr
  exact ⟨b,hw,.trans e d⟩

private theorem reflView {S K C t q} (h : NumberedWindowDomain.Typed C q t) : LamView S K C t q q := by
  rintro σ τ v rfl rfl
  cases h with
  | lam hb => exact ⟨_,rfl,.refl hb⟩

private theorem both {S K C t q r} (p : Primary S K C t q r) :
    LamView S K C t q r ∧ LamView S K C t r q := by
  induction p using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | refl h => exact ⟨reflView h,reflView h⟩
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact ⟨transView one.1 two.1, transView two.2 one.2⟩
  | lam e _ =>
    constructor
    · rintro σ τ v eq hv
      cases eq
      cases hv
      exact ⟨_,rfl,e⟩
    · rintro σ τ v eq hv
      cases eq
      cases hv
      exact ⟨_,rfl,.symm e⟩
  | _ => first | exact True.intro | constructor <;> intro σ τ v _ eq <;> cases eq

theorem components : PrimaryLambdaComponents := by
  intro S K C σ τ v out h
  exact (both h).1 σ τ v rfl rfl

private theorem rawLambda {S K σ v out} (h : RawStep S K (.lam σ v) out) :
    out = .bottom (.arrow σ v.type) ∨ ∃ w, RawStep S K v w ∧ out = .lam σ w := by
  cases h with
  | bottom _ => exact .inl rfl
  | lam e => exact .inr ⟨_,e,rfl⟩

theorem edges : LambdaEdges := by
  intro S K C σ τ hk hτ v out
  refine Quot.inductionOn v ?_
  intro V h
  obtain ⟨a,b,ea,eb,raw⟩ := h
  have p := primaryOfClassEquality (lamCarrier hk hτ V) a ea.symm
  obtain ⟨body,ha,primary⟩ := components S K C σ τ V.val a.val p
  have wa : InWindow S K C (.arrow σ τ) (.lam σ body) := ha ▸ a.property
  let A : WindowCarrier S K (C.push σ) τ := ⟨body,lamBody wa⟩
  have hA : classOf A = classOf V := Quot.sound primary.symm
  have step : RawStep S K (.lam σ body) b.val := ha ▸ raw
  rcases rawLambda step with hBot | ⟨w,hw,hb⟩
  · have ht := NumberedWindowApplicationDomainProof.annotation A.property.1
    exact Or.inl ⟨b,by simpa only [show body.type = τ from ht] using hBot,eb⟩
  · have wb : InWindow S K C (.arrow σ τ) (.lam σ w) := hb ▸ b.property
    let B : WindowCarrier S K (C.push σ) τ := ⟨w,lamBody wb⟩
    have hB : b = lamCarrier hk hτ B := Subtype.ext hb
    exact .inr ⟨classOf B, ⟨A,B,hA,rfl,hw⟩, eb.symm.trans (congrArg classOf hB)⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalLambdaShapeProof
