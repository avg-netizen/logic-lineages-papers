module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAdvanceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicPositivePathProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicPositiveTargets
open NumberedWindowConcreteCheckers (step)
open NumberedWindowScalarAlgorithm (least)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPositivePathAlgorithm (Step Least advance walk positive)
open NumberedWindowAtomicPositiveAdvanceProof (atomAdvance)

private theorem failureAbsorbs (runStep : Nat → Nat → Nat → Bool) (leastOf : Nat → Option Nat)
    (codes : List Nat) : codes.foldl (advance runStep leastOf) none = none := by
  induction codes with
  | nil => rfl
  | cons h hs ih =>
    change hs.foldl (advance runStep leastOf) none = none
    exact ih

private theorem actualNonemptyFold (runStep : Step) (leastOf : Least) (Γ : List Nat)
    (requested source witness y : Nat)
    (h : positive runStep leastOf Γ requested source witness y = true) :
    ∃ code tail, unpack witness = some (code :: tail) ∧
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

theorem atomPositivePath : ExactConcreteAtomicPositivePath := by
  constructor
  · intro xs s Γ requested t n witness y h
    let a := advance (step xs s Γ requested) (least s Γ requested)
    obtain ⟨code,tail,unpacked,found⟩ :=
      actualNonemptyFold (step xs s) (least s) Γ requested (freeRaw t n) witness y h
    change tail.foldl a (a (some (freeRaw t n)) code) = some y at found
    cases ha : a (some (freeRaw t n)) code with
    | none =>
      rw [ha,failureAbsorbs] at found
      cases found
    | some first =>
      have hFirst := atomAdvance.1 xs s Γ requested t n code first ha
      rw [ha] at found
      cases tail with
      | nil =>
        have same : first = y := Option.some.inj found
        subst y
        exact ⟨hFirst.1,hFirst.2.1,hFirst.2.2,code,unpacked,ha⟩
      | cons next suffix =>
        have hn : a (some first) next = none := by
          rw [hFirst.1]
          exact atomAdvance.2 xs s Γ requested t next
        rw [List.foldl_cons,hn,failureAbsorbs] at found
        cases found
  · intro xs s Γ requested t witness y
    cases h : positive (step xs s) (least s) Γ requested (bottomRaw t) witness y with
    | false => rfl
    | true =>
      obtain ⟨code,tail,_,found⟩ :=
        actualNonemptyFold (step xs s) (least s) Γ requested (bottomRaw t) witness y h
      rw [atomAdvance.2 xs s Γ requested t code,failureAbsorbs] at found
      cases found

end LogicLineages.PersistentMarking.NumberedWindowAtomicPositivePathProof
