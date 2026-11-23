module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationGuardProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalNeutralEdgesProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowRules
open NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowExternalNeutralTargets NumberedWindowExternalNeutralPrimaryProof
open NumberedWindowPreservationGuardProof (appParts)

theorem application : NonLambdaApplicationClass := by
  intro S K C σ τ hk q u
  refine Quot.inductionOn q ?_
  intro f
  refine Quot.inductionOn u ?_
  intro a
  apply (representatives S K C τ (appCarrier hk f a)).mpr
  intro ρ body h
  cases h

private theorem rawCases {S K σ τ q u out} (hn : NonLambda q)
    (h : RawStep S K (.auxApp σ τ q u) out) :
    out = .bottom τ ∨ ∃ r, RawStep S K q r ∧ out = .auxApp σ τ r u := by
  cases h with
  | beta => exact False.elim (hn _ _ rfl)
  | bottom _ => exact .inl rfl
  | auxFunction step => exact .inr ⟨_, step, rfl⟩

theorem edges : NeutralApplicationEdges := by
  intro S K C σ τ hk q u out
  refine Quot.inductionOn q ?_
  intro f
  refine Quot.inductionOn u ?_
  intro a hn hEdge
  change ClassNonLambda (classOf f) at hn
  change ClassEdge (classOf (appCarrier hk f a)) out at hEdge
  obtain ⟨before, after, hBefore, hAfter, hRaw⟩ := hEdge
  have hPrimary := primaryOfClassEquality (appCarrier hk f a) before hBefore.symm
  obtain ⟨g, b, hShape, hFunction, hArgument⟩ := applicationComponents S K C σ τ f.val a.val before.val hPrimary
  have hBeforeWindow : InWindow S K C τ (.auxApp σ τ g b) := hShape ▸ before.property
  obtain ⟨hg, hb⟩ := appParts hBeforeWindow
  let fn : WindowCarrier S K C (.arrow σ τ) := ⟨g, hg⟩
  let arg : WindowCarrier S K C σ := ⟨b, hb⟩
  have hFn : classOf fn = classOf f := Quot.sound (.symm hFunction)
  have hArg : classOf arg = classOf a := Quot.sound (.symm hArgument)
  have hStep : RawStep S K (.auxApp σ τ g b) after.val := hShape ▸ hRaw
  rcases rawCases (hn fn hFn) hStep with hBottom | ⟨r, hChange, hResult⟩
  · exact .inl ⟨after, hBottom, hAfter⟩
  · have hAfterWindow : InWindow S K C τ (.auxApp σ τ r b) := hResult ▸ after.property
    let next : WindowCarrier S K C (.arrow σ τ) := ⟨r, (appParts hAfterWindow).1⟩
    refine .inr ⟨classOf next, ⟨fn, next, hFn, rfl, hChange⟩, ?_⟩
    have hApplied : after = appCarrier hk next arg := Subtype.ext hResult
    calc
      out = classOf after := hAfter.symm
      _ = classOf (appCarrier hk next arg) := congrArg classOf hApplied
      _ = appClass hk (classOf next) (classOf arg) := rfl
      _ = appClass hk (classOf next) (classOf a) := congrArg (appClass hk (classOf next)) hArg

end LogicLineages.PersistentMarking.NumberedWindowExternalNeutralEdgesProof
