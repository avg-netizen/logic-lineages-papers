module
public import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsHopProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsWalkProof
open NumberedWindowConcretePositiveEndpointsTargets
open NumberedWindowConcretePositiveEndpointsHopProof (hopReport)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPositivePathAlgorithm (Step Least advance positive walk)
open NumberedWindowScalarAlgorithm (least)
open NumberedWindowConcreteCheckers (step)

private theorem failureAbsorbs (runStep : Nat → Nat → Nat → Bool) (leastOf : Nat → Option Nat)
    (codes : List Nat) : codes.foldl (advance runStep leastOf) none = none := by
  induction codes with
  | nil => rfl
  | cons h hs ih =>
    change hs.foldl (advance runStep leastOf) none = none
    exact ih

private theorem actualNonemptyFold (runStep : Step) (leastOf : Least) (ctx : List Nat)
    (ty source witness target : Nat)
    (h : positive runStep leastOf ctx ty source witness target = true) :
    ∃ first rest, unpack witness = some (first :: rest) ∧
      (first :: rest).foldl (advance (runStep ctx ty) (leastOf ctx ty))
        (some source) = some target := by
  cases hu : unpack witness with
  | none => simp [positive,hu] at h
  | some codes =>
    cases codes with
    | nil => simp [positive,hu] at h
    | cons first rest =>
      refine ⟨first,rest,?_,?_⟩
      · first | exact hu | rfl
      · simpa [positive,walk,hu,beq_iff_eq] using h

private theorem splitLast (first : Nat) (rest : List Nat) :
    ∃ beforeLast last, first :: rest = beforeLast ++ [last] := by
  induction rest generalizing first with
  | nil => exact ⟨[],first,rfl⟩
  | cons a rest ih =>
    obtain ⟨beforeLast,last,same⟩ := ih a
    exact ⟨first :: beforeLast,last,congrArg (List.cons first) same⟩

theorem boundaryHops : ExactConcretePositiveBoundaryHops := by
  intro entries s ctx ty source witness target ok
  let a := advance (step entries s ctx ty) (least s ctx ty)
  obtain ⟨first,rest,supplied,found⟩ :=
    actualNonemptyFold (step entries s) (least s) ctx ty source witness target ok
  change (first :: rest).foldl a (some source) = some target at found
  obtain ⟨beforeLast,last,cut⟩ := splitLast first rest
  have firstExists : ∃ firstOut, a (some source) first = some firstOut := by
    cases report : a (some source) first with
    | none =>
      rw [List.foldl_cons,report] at found
      change rest.foldl (advance (step entries s ctx ty) (least s ctx ty)) none = some target at found
      rw [failureAbsorbs] at found
      cases found
    | some firstOut => exact ⟨firstOut,by first | exact report | rfl⟩
  obtain ⟨firstOut,firstReport⟩ := firstExists
  have lastFold : a (beforeLast.foldl a (some source)) last = some target := by
    rw [cut,List.foldl_append] at found
    exact found
  cases report : beforeLast.foldl a (some source) with
  | none =>
    rw [report] at lastFold
    change none = some target at lastFold
    cases lastFold
  | some lastIn =>
    rw [report] at lastFold
    exact ⟨first :: rest,first,rest,beforeLast,last,firstOut,lastIn,supplied,rfl,cut,
      firstReport,report,lastFold,hopReport entries s ctx ty source first firstOut firstReport,
        hopReport entries s ctx ty lastIn last target lastFold⟩

end LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsWalkProof
