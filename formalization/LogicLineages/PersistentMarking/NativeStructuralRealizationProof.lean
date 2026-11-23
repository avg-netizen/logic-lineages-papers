import LogicLineages.PersistentMarking.NativeStructuralRealizationTargets
import LogicLineages.PersistentMarking.NativeStructuralRealizationBetaProof

namespace LogicLineages.PersistentMarking.NativeStructuralRealizationProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeStructuralRealizationSyntax NativeStructuralRealizationClosingProof
open NativeStructuralRealizationBetaProof NativeStructuralRealizationTargets

private theorem extend (R : Relation S Base) (ρ : ClosedEnv S Γ) (θ : ValueEnv Base Γ)
    (agree : Respects R ρ θ) (x : Value Base A) (u : ClosedNativeTerm S (actualType A))
    (hx : R A u x) : Respects R (.cons u ρ) (.cons x θ) := by
  intro D i
  cases i with
  | here => exact hx
  | there i => exact agree _ i

theorem exact_StructuralNativeRealization : ExactStructuralNativeRealization := by
  intro Base S C lit meaning R arrows backward constants Γ A t
  induction t with
  | var i =>
    intro ρ θ agree
    rw [instantiatedVar]
    exact agree _ i
  | app A D f u hf hu =>
    intro ρ θ agree
    rw [instantiatedApp]
    exact (arrows A D _ _).mp (hf ρ θ agree) _ _ (hu ρ θ agree)
  | @lam Γ D A t ih =>
    intro ρ θ agree
    apply (arrows A D _ _).mpr
    intro x u hx
    have child := ih (.cons u ρ) (.cons x θ) (extend R ρ θ agree x u hx)
    have edge := (exact_StructuralNativeBeta S C lit Γ A D t ρ u).2
    exact backward D _ _ _ edge child
  | literal k =>
    intro ρ θ agree
    rw [instantiatedConstant]
    exact constants _ k

end LogicLineages.PersistentMarking.NativeStructuralRealizationProof
