module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsHopProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineZeroPathProof
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpinePositiveRankProof
  (exact_OriginalNeutralRankLeast exact_OriginalNeutralRankAdvance)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)
open NumberedWindowConcretePositiveEndpointsHopProof (hopReport)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowPositivePathAlgorithm (advance positive walk hopView)
open NumberedWindowFieldAlgorithm (unpack)

private theorem noReturn (f : Nat → Nat → Nat → Bool) (L : Nat → Option Nat) :
    ∀ codes : List Nat, codes.foldl (advance f L) none = none := by
  intro codes
  induction codes with
  | nil => rfl
  | cons c cs ih => exact ih

private theorem nonzeroFinal (xs : Entries) (s : Settings) (ctx : List Nat) (ty : Nat) :
    ∀ (codes : List Nat) (a b : Nat), rawRank a ≠ 0 →
      codes.foldl (advance (step xs s ctx ty) (least s ctx ty)) (some a) = some b →
      rawRank b ≠ 0 := by
  intro codes
  induction codes with
  | nil =>
    intro a b ranked eq
    have state : a = b := Option.some.inj eq
    exact state ▸ ranked
  | cons c cs ih =>
    intro a b ranked folded
    rw [List.foldl_cons] at folded
    cases one : advance (step xs s ctx ty) (least s ctx ty) (some a) c with
    | none =>
      rw [one,noReturn] at folded
      cases folded
    | some mid =>
      have live := (exact_OriginalNeutralRankAdvance xs s (exact_OriginalKeepsNeutralRank s)
        ctx ty a c mid ranked one).1
      rw [one] at folded
      exact ih mid b live folded

private theorem foldedOriginal (xs : Entries) (s : Settings) (ctx : List Nat)
    (ty src cert dst : Nat) (codes : List Nat) (spine : unpack cert = some codes)
    (actual : positive (step xs s) (least s) ctx ty src cert dst = true) :
    codes.foldl (advance (step xs s ctx ty) (least s ctx ty)) (some src) = some dst := by
  cases codes with
  | nil => simp [positive,spine] at actual
  | cons c cs => simpa [positive,walk,spine,beq_iff_eq] using actual

/-- The actual original certificate's suffix cannot come back from a
positive neutral rank to zero. Opening any exact prefix therefore
recovers its own genuine zero-rank selected intermediate. -/
theorem exact_OriginalZeroEndpointPathPrefix (xs : Entries) (s : Settings) (ctx : List Nat)
    (ty src cert dst : Nat) (head tail : List Nat)
    (split : unpack cert = some (head ++ tail))
    (actual : positive (step xs s) (least s) ctx ty src cert dst = true)
    (lastZero : rawRank dst = 0) :
    let a := advance (step xs s ctx ty) (least s ctx ty)
    ∃ mid, head.foldl a (some src) = some mid ∧ rawRank mid = 0 ∧
      tail.foldl a (some mid) = some dst := by
  let a := advance (step xs s ctx ty) (least s ctx ty)
  have endEq : (head ++ tail).foldl a (some src) = some dst :=
    foldedOriginal xs s ctx ty src cert dst (head ++ tail) split actual
  rw [List.foldl_append] at endEq
  cases h : head.foldl a (some src) with
  | none =>
    rw [h] at endEq
    change tail.foldl (advance (step xs s ctx ty) (least s ctx ty)) none = some dst at endEq
    rw [noReturn] at endEq
    cases endEq
  | some mid =>
    rw [h] at endEq
    have zero : rawRank mid = 0 := by
      by_cases known : rawRank mid = 0
      · exact known
      · exact False.elim ((nonzeroFinal xs s ctx ty tail mid dst known endEq) lastZero)
    exact ⟨mid,h,zero,endEq⟩

/-- Each real head row selected by a split of the very same original
certificate uses unranked source and destination raw codes if the
actual visible endpoint has rank zero. No alternate witness is chosen. -/
theorem exact_OriginalZeroEndpointPathRow (xs : Entries) (s : Settings) (ctx : List Nat)
    (ty src cert dst code : Nat) (head tail : List Nat)
    (split : unpack cert = some (head ++ code :: tail))
    (actual : positive (step xs s) (least s) ctx ty src cert dst = true)
    (lastZero : rawRank dst = 0) :
    let a := advance (step xs s ctx ty) (least s ctx ty)
    ∃ left right q w y, head.foldl a (some src) = some left ∧
      a (some left) code = some right ∧ hopView code = some (right,q,w,y) ∧
      rawRank left = 0 ∧ rawRank right = 0 ∧ rawRank q = 0 ∧ rawRank y = 0 := by
  let a := advance (step xs s ctx ty) (least s ctx ty)
  obtain ⟨left,first,lz,after⟩ :=
    exact_OriginalZeroEndpointPathPrefix xs s ctx ty src cert dst head (code :: tail)
      split actual lastZero
  change (code :: tail).foldl a (some left) = some dst at after
  rw [List.foldl_cons] at after
  cases h : a (some left) code with
  | none =>
    rw [h] at after
    change tail.foldl (advance (step xs s ctx ty) (least s ctx ty)) none = some dst at after
    rw [noReturn] at after
    cases after
  | some right =>
    rw [h] at after
    have rz : rawRank right = 0 := by
      by_cases known : rawRank right = 0
      · exact known
      · exact False.elim ((nonzeroFinal xs s ctx ty tail right dst known after) lastZero)
    obtain ⟨q,w,y,original,_,_,_,qLeast,yLeast⟩ := hopReport xs s ctx ty left code right h
    have qz := (exact_OriginalNeutralRankLeast s (exact_OriginalKeepsNeutralRank s)
      ctx ty q left qLeast).symm.trans lz
    have yz := (exact_OriginalNeutralRankLeast s (exact_OriginalKeepsNeutralRank s)
      ctx ty y right yLeast).symm.trans rz
    exact ⟨left,right,q,w,y,first,h,original,lz,rz,qz,yz⟩

#print axioms exact_OriginalZeroEndpointPathPrefix
#print axioms exact_OriginalZeroEndpointPathRow
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineZeroPathProof
