module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionAdvanceProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionPathProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationReductionAdvanceProof (auxAdvance image bottomFunctionImage)
open NumberedWindowAtomicPositiveChecks (exact_ConcreteAtomicAdvance)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowScalarAlgorithm (least)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPositivePathAlgorithm (Step Least advance positive walk)

private theorem failureAbsorbs (runStep : Nat → Nat → Nat → Bool) (leastOf : Nat → Option Nat)
    (codes : List Nat) : codes.foldl (advance runStep leastOf) none = none := by
  induction codes with
  | nil => rfl
  | cons code rest ih =>
    change rest.foldl (advance runStep leastOf) none = none
    exact ih

private theorem actualNonemptyFold (runStep : Step) (leastOf : Least) (Γ : List Nat)
    (requested source witness y : Nat)
    (h : positive runStep leastOf Γ requested source witness y = true) :
    ∃ code tail, unpack witness = some (code::tail) ∧
      tail.foldl (advance (runStep Γ requested) (leastOf Γ requested))
        (advance (runStep Γ requested) (leastOf Γ requested) (some source) code) = some y := by
  cases hu : unpack witness with
  | none => simp [positive,hu] at h
  | some codes =>
    cases codes with
    | nil => simp [positive,hu] at h
    | cons code tail =>
      refine ⟨code,tail,?_,?_⟩
      · first | exact hu | rfl
      · simpa [positive,walk,hu,beq_iff_eq] using h

theorem auxPositivePath : ExactAtomicAuxPositivePath := by
  intro xs s Γ requested dom cod fn arg witness y atom checked
  let a := advance (step xs s Γ requested) (least s Γ requested)
  let source := auxRaw dom cod fn arg
  obtain ⟨e₀,tail,actual,success⟩ :=
    actualNonemptyFold (step xs s) (least s) Γ requested source witness y checked
  change tail.foldl a (a (some source) e₀) = some y at success
  cases h₀ : a (some source) e₀ with
  | none =>
    rw [h₀,failureAbsorbs] at success
    cases success
  | some firstValue =>
    have hop₀ := auxAdvance xs s Γ requested dom cod fn arg e₀ firstValue atom h₀
    rw [h₀] at success
    cases tail with
    | nil =>
      have same : firstValue = y := Option.some.inj success
      subst y
      exact Or.inl ⟨e₀,actual,h₀,hop₀⟩
    | cons e₁ suffix =>
      rcases image hop₀ with atBottom | ⟨stored,name,midArg,headFree,midShape⟩
      · have blocked : a (some firstValue) e₁ = none := by
          rw [atBottom]
          exact exact_ConcreteAtomicAdvance.2 xs s Γ requested cod e₁
        rw [List.foldl_cons,blocked,failureAbsorbs] at success
        cases success
      · let mid := auxRaw dom cod (bottomRaw stored) midArg
        rw [midShape] at success h₀ hop₀
        change suffix.foldl a (a (some mid) e₁) = some y at success
        cases h₁ : a (some mid) e₁ with
        | none =>
          rw [h₁,failureAbsorbs] at success
          cases success
        | some secondValue =>
          have hop₁ := auxAdvance xs s Γ requested dom cod (bottomRaw stored) midArg e₁ secondValue
            (AtomHead.bottom stored) h₁
          have reachedBottom := bottomFunctionImage hop₁
          rw [h₁] at success
          cases suffix with
          | nil =>
            have same : secondValue = y := Option.some.inj success
            subst y
            exact Or.inr ⟨e₀,e₁,stored,name,midArg,headFree,actual,h₀,hop₀,h₁,hop₁,reachedBottom⟩
          | cons e₂ rest =>
            have blocked : a (some secondValue) e₂ = none := by
              rw [reachedBottom]
              exact exact_ConcreteAtomicAdvance.2 xs s Γ requested cod e₂
            rw [List.foldl_cons,blocked,failureAbsorbs] at success
            cases success

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionPathProof
