module

public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaStrictProof
open Spine NameBridge

theorem lift (S : Signature) (σ τ : Ty) (x : Nat) (src target : Expr)
    (hp : PaperTerm S (.lam σ src) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ target) (.arrow σ τ))
    (hs : freeOccurs (σ,x) src = false) (hT : freeOccurs (σ,x) target = false)
    (h : Strict S (openBody σ x src) (openBody σ x target)) :
    Strict S (.lam σ src) (.lam σ target) := by
  cases h with
  | @intro _ _ ρ r _ _ hr hWeak =>
    have hm := RefinementMarkProof.markOpenMap σ x 0 src
    change mark (openBody σ x src) = (mark src).map (openBody σ x) at hm
    cases hSrc : mark src with
    | none =>
      rw [hSrc,Option.map_none,hr] at hm
      cases hm
    | some m =>
      rw [hSrc,Option.map_some,hr] at hm
      have hEq := Option.some.inj hm
      subst r
      have hmLam : mark (.lam σ src) = some (.lam σ m) := by simp [mark,hSrc]
      have hMarked := RefinementMarkProof.markPaper S _ (.arrow σ τ) _ hp hmLam
      have hFresh : freeOccurs (σ,x) m = false :=
        (ElementarySupportProof.markNames (σ,x) src m hSrc).symm.trans hs
      exact .intro hp ht hmLam (.abs hMarked ht hFresh hT hWeak)

end LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaStrictProof
