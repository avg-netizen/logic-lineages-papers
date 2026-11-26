import LogicLineages.PersistentMarking.ProtectedSpineStrictFieldLambdaStep

namespace LogicLineages.PersistentMarking.ProtectedSpineStrictMarkThinProof
open Spine DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineStrictTargets ProtectedSpineStrictFieldLambdaStep

theorem all (S : Signature) (E : Environment) (H : List Head) (M : Code) :
    ∀ q, Point S E H M q :=
  @Expr.rec (Point S E H M) (fun _ => True)
    (fun σ x Γ Δ a t _ _ hs hd he ht => (hs Δ hd he σ t ht).1 x)
    (fun σ i Γ Δ a t _ _ hs hd he ht => (hs Δ hd he σ t ht).2 i)
    (step S E H M)
    (fun _ _ _ => by intro Γ Δ a t hq ha hs hd he ht; rfl)
    (fun _ _ _ _ _ _ => by intro Γ Δ a t hq ha hs hd he ht; rfl)
    True.intro
    (fun _ _ _ _ => True.intro)

theorem exact_MarkingFields : MarkingFields := by
  intro S E H M Γ Δ a q t
  exact all S E H M q Γ Δ a t

#print axioms exact_MarkingFields

end LogicLineages.PersistentMarking.ProtectedSpineStrictMarkThinProof
