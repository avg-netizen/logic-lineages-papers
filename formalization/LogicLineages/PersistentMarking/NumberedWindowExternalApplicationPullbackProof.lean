import LogicLineages.PersistentMarking.NumberedWindowExternalScalarClassProof
import LogicLineages.PersistentMarking.NumberedWindowExternalApplicationPathProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalApplicationPullbackProof
open NumberedWindowExternalApplicationTargets NumberedWindowExternalApplication
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass

private theorem accPull {α β : Type} {R : α → α → Prop} {T : β → β → Prop}
    (f : α → β) (preserves : ∀ q r, R r q → T (f r) (f q)) {b : β} (hb : Acc T b) :
    ∀ q, f q = b → Acc R q := by
  induction hb with
  | intro b _ ih =>
    intro q eq
    constructor
    intro r h
    exact ih (f r) (eq ▸ preserves q r h) r rfl

theorem pullback : ExternalIApplicationPullback := by
  intro S K Γ σ τ hk q u i j hi hj hApp
  have acc := (NumberedWindowExternalScalarClassProof.scalarClass
    S K Γ τ hk (appClass hk q u) j hj).mp hApp
  apply (NumberedWindowExternalScalarClassProof.scalarClass S K Γ (.arrow σ τ) hk q i hi).mpr
  exact accPull (fun x : Class S K (finiteC Γ) (.arrow σ τ) => appClass hk x u)
    (fun x y h => NumberedWindowExternalApplicationPathProof.positive
      S K (finiteC Γ) σ τ hk x y u h) acc q rfl

end LogicLineages.PersistentMarking.NumberedWindowExternalApplicationPullbackProof
