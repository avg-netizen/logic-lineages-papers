import LogicLineages.PersistentMarking.MarkedConstructorTargets
import LogicLineages.PersistentMarking.HereditaryEncodeDecodeProof
import LogicLineages.PersistentMarking.StructuralWholeBottomProof

namespace LogicLineages.PersistentMarking.MarkedConstructorLiteralProof
open Spine DecisionPorts HereditaryDomainCode HereditaryDomainSemantics ProtectedSpineEnvironment

theorem literalValid (E : Environment) (σ : Ty) (Γ : Context) (x : Nat) :
    Valid E σ Γ (literal E σ x) := by
  refine ⟨?_,?_,?_⟩
  · intro Δ hd _ ds τ _ xs _
    exact (StructuralWholeBottomProof.wholeBottom E τ Δ hd).1
  · intro Δ hd _ ds τ _ xs ys _ _ _
    exact (HereditaryPartialOrderProof.partialOrder E τ Δ hd).1 _
      (StructuralWholeBottomProof.wholeBottom E τ Δ hd).1
  · intro Δ Θ hd ht _ he ds τ _ xs _
    exact (HereditaryLatticeInductionProof.restriction E τ Δ Θ [] hd ht he (by simp)).1

theorem literalRetained (E : Environment) (Γ : Context) (σ : Ty) (x : Nat)
    (hw : WellFormed E.types E.ports Γ) : literalCode E Γ σ x ∈ (descriptor E σ).carriers Γ :=
  (HereditaryEncodeDecodeProof.encodeDecode E σ Γ (literal E σ x) hw (literalValid E σ Γ x)).1

end LogicLineages.PersistentMarking.MarkedConstructorLiteralProof
