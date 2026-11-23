import LogicLineages.PersistentMarking.NativeStructuralRealizationClosingProof
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.BoundBlockProof

namespace LogicLineages.PersistentMarking.NativeStructuralRealizationBetaProof
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication NativeStructuralRealizationSyntax
open NativeStructuralRealizationClosingProof

/-- One real native beta step after the outer environment has been
substituted under the binder. The endpoint uses the original cons-order
simultaneous substitution, not a separate evaluation model. -/
def ExactStructuralNativeBeta : Prop :=
  ∀ (S : Signature) (C : SemanticType → Type) (lit : Literals S C)
    (Γ : List SemanticType) (A D : SemanticType) (t : Fragment C (A :: Γ) D)
    (ρ : ClosedEnv S Γ) (u : ClosedNativeTerm S (actualType A)),
    let start := applyClosed (instantiate lit (.lam A t) ρ) u
    let finish := instantiate lit t (.cons u ρ)
    Reduction S start.val finish.val ∧ NativeBelow finish start

theorem exact_StructuralNativeBeta : ExactStructuralNativeBeta := by
  intro S C lit Γ A D t ρ u start finish
  let body := substitute ρ.args 1 (t.raw lit)
  have hl : ClosedNative S (.lam (actualType A) body) (.arrow (actualType A) (actualType D)) :=
    (instantiate lit (.lam A t) ρ).property
  obtain ⟨result,value,step,strict⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S (actualType A) (actualType D) body hl u
  have stacked : substitute (.cons u.val .nil) 0 body = finish.val :=
    BoundBlockProof.block (.cons u.val .nil) ρ.args 0 (t.raw lit)
  have eq : result = finish := Subtype.ext (value.trans stacked)
  subst result
  exact ⟨step,strict⟩

end LogicLineages.PersistentMarking.NativeStructuralRealizationBetaProof
