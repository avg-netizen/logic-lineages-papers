import LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathProof
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowExternalInstance NumberedWindowExternalSubstitutionTargets
open NumberedWindowExternalWindowSubstitutionChecks NumberedWindowExternalInstancePathTargets

theorem edgeOrEqual : InstanceClassEdgeOrEqual := by
  intro S K C σ τ hk v w u
  refine Quot.inductionOn u ?_
  intro U step
  obtain ⟨a,b,rfl,rfl,raw⟩ := step
  have win : WindowStep S K (C.push σ) τ a.val b.val := ⟨raw,a.property,b.property⟩
  rcases exact_SubstitutionWindowStep S K (C.push σ) C τ a.val b.val (.cons U.val .nil) 0
    hk (NumberedWindowPreservationBoundProof.one hk U.property) win with change | ⟨eq,_⟩
  · exact .inl ⟨bodyInstance hk a U,bodyInstance hk b U,rfl,rfl,change.1⟩
  · have equal : bodyInstance hk a U = bodyInstance hk b U := Subtype.ext eq
    exact .inr (congrArg classOf equal)

private theorem freeEdge {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    {v w : Class S K (BoundContext.push C σ) τ} (u : WindowCarrier S K C σ) (i : Nat)
    (hu : u.val = .free σ i) (step : ClassEdge v w) :
    ClassEdge (instanceClass hk v (classOf u)) (instanceClass hk w (classOf u)) := by
  obtain ⟨a,b,rfl,rfl,raw⟩ := step
  have win : WindowStep S K (C.push σ) τ a.val b.val := ⟨raw,a.property,b.property⟩
  have hσ := NumberedWindowApplicationDomainProof.rootInWindow u.property
  have e := exact_FreeSubstitutionWindowStep S K C σ τ a.val b.val i hk hσ win
  refine ⟨bodyInstance hk a u,bodyInstance hk b u,rfl,rfl,?_⟩
  simpa only [bodyInstance,hu] using e.1

theorem freePositive : FreeInstancePreservesPositive := by
  intro S K C σ τ hk v w u i hu path
  induction path with
  | one edge => exact .one (freeEdge hk u i hu edge)
  | more edge _ ih => exact .more (freeEdge hk u i hu edge) ih

private theorem pull {α β : Type} {R : α → α → Prop} {T : β → β → Prop}
    (f : α → β) (preserves : ∀ q r, R r q → T (f r) (f q)) {b : β} (h : Acc T b) :
    ∀ q, f q = b → Acc R q := by
  induction h with
  | intro b _ ih =>
    intro q eq
    constructor
    intro r hr
    exact ih (f r) (eq ▸ preserves q r hr) r rfl

theorem reflect : FreeInstanceReflectsAccessibility := by
  intro S K C σ τ hk v u i hu h
  exact pull (fun w : Class S K (C.push σ) τ => instanceClass hk w (classOf u))
    (fun x y => freePositive S K C σ τ hk x y u i hu) h v rfl

end LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathProof
