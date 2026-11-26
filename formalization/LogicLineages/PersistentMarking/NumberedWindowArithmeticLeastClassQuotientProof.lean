import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassEqualityProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassQuotientProof
open NumberedWindowSyntax NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassTargets

/-- A Setoid presentation of the very same relation used by Class, solely
to apply the standard effectiveness of a quotient by an equivalence. -/
private def actualSetoid (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (τ : Ty) : Setoid (WindowCarrier S K C τ) where
  r x y := Primary S K C τ x.val y.val
  iseqv :=
    ⟨fun x => .refl x.property.1, fun h => .symm h, fun e d => .trans e d⟩

private theorem originalQuotient {S K C τ} (Q R : WindowCarrier S K C τ) :
    Primary S K C τ Q.val R.val ↔ classOf Q = classOf R := by
  constructor
  · intro h
    exact Quot.sound h
  · intro h
    have e : Quotient.mk (actualSetoid S K C τ) Q =
        Quotient.mk (actualSetoid S K C τ) R := h
    exact Quotient.exact e

theorem quotientEq : LeastCodeReflectsActualQuotient := by
  intro S K Γ τ Q R hk
  exact (NumberedWindowArithmeticLeastClassEqualityProof.leastEq
    S K Γ τ Q.val R.val hk Q.property R.property).trans (originalQuotient Q R)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassQuotientProof
