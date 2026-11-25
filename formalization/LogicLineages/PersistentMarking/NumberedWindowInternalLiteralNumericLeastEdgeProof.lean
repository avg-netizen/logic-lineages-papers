module
public import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationChecks
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericLeastEdgeProof
open NumberedWindowClassAlgorithm (advance rounds members)
open NumberedWindowScalarAlgorithm (Settings admitted edge vertices least)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowRawExchangeSymmetryChecks (exact_ScalarEdgeSymmetry)
open NumberedWindowRawExchangeVerticesChecks (exact_OriginalGuardedEdgeVertices)
open NumberedWindowRawClassSaturationChecks (exact_LiteralClassSaturation)

private theorem seenIff {step : Nat → Nat → Bool} {pool seen : List Nat} {v : Nat} :
    v ∈ advance step pool seen ↔ v ∈ pool ∧ ∃ w, w ∈ seen ∧ (w = v ∨ step w v = true) := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq]

private theorem seedStays (step : Nat → Nat → Bool) (pool : List Nat) (y : Nat)
    (inPool : y ∈ pool) : ∀ fuel, y ∈ rounds step pool y fuel := by
  intro fuel
  induction fuel with
  | zero => simp [rounds,inPool]
  | succ fuel ih => exact ((exact_LiteralClassSaturation step pool y).2.1 fuel).subset ih

private theorem inClosed (step : Nat → Nat → Bool) (pool : List Nat) (seed a : Nat)
    (hit : a ∈ members step pool seed) (fuel : Nat) :
    ∀ x ∈ rounds step pool a fuel, x ∈ members step pool seed := by
  induction fuel with
  | zero =>
    intro x h
    simp only [rounds,List.mem_filter,beq_iff_eq] at h
    exact h.2 ▸ hit
  | succ fuel ih =>
    intro x hx
    change x ∈ advance step pool (rounds step pool a fuel) at hx
    obtain ⟨inPool,w,prior,go⟩ := seenIff.mp hx
    rw [← (exact_LiteralClassSaturation step pool seed).2.2]
    exact seenIff.mpr ⟨inPool,w,ih w prior,go⟩

private theorem follows (step : Nat → Nat → Bool) (pool : List Nat) (a b : Nat)
    (ha : a ∈ pool) (hb : b ∈ pool) (ab : step a b = true) : b ∈ members step pool a := by
  rw [← (exact_LiteralClassSaturation step pool a).2.2]
  exact seenIff.mpr ⟨hb,a,seedStays step pool a ha pool.length,Or.inr ab⟩

/-- The two numeric minimum calls are exactly equal on a real
bidirectional edge, with the same original list and both seeds
present. No change of executable least or use of open correctness. -/
theorem exact_LiteralNumericSamePoolLeastEdge (step : Nat → Nat → Bool) (pool : List Nat)
    (a b : Nat) (ha : a ∈ pool) (hb : b ∈ pool) (ab : step a b = true) (ba : step b a = true) :
    NumberedWindowClassAlgorithm.least step pool a = NumberedWindowClassAlgorithm.least step pool b := by
  let ma := members step pool a
  let mb := members step pool b
  have ab' : ∀ x ∈ ma, x ∈ mb := inClosed step pool b a (follows step pool b a hb ha ba) pool.length
  have ba' : ∀ x ∈ mb, x ∈ ma := inClosed step pool a b (follows step pool a b ha hb ab) pool.length
  change ma.min? = mb.min?
  cases l : ma.min? with
  | none =>
    have empty := List.min?_eq_none_iff.mp l
    have inside : a ∈ ma := seedStays step pool a ha pool.length
    simp [empty] at inside
  | some k =>
    obtain ⟨member,lower⟩ := List.min?_eq_some_iff.mp l
    exact (List.min?_eq_some_iff.mpr ⟨ab' k member,fun x h => lower x (ba' x h)⟩).symm

/-- The unchanged original raw scalar edge gives same least on the
ordered physical covers. All three relevant hypotheses (actual
admission, original cover equality, and symmetry) are explicit or
taken from the already verified original numeric invariants. -/
theorem exact_LiteralNumericLeastEdge (s : Settings) (covered : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (ctx : List Nat) (ty a b : Nat)
    (ab : edge s ctx ty a b = true) : least s ctx ty a = least s ctx ty b := by
  have admittedBoth : admitted s ctx ty a = true ∧ admitted s ctx ty b = true := by
    simp only [edge,Bool.and_eq_true] at ab
    exact ⟨ab.1.2,ab.2⟩
  have same := exact_OriginalGuardedEdgeVertices s ctx ty a b ab
  have ba : edge s ctx ty b a = true := by
    rw [exact_ScalarEdgeSymmetry s symmetric ctx ty b a]
    exact ab
  have hs := covered ctx ty a admittedBoth.1
  have ht := covered ctx ty b admittedBoth.2
  change NumberedWindowClassAlgorithm.least (edge s ctx ty) (vertices s a) a =
    NumberedWindowClassAlgorithm.least (edge s ctx ty) (vertices s b) b
  rw [same]
  exact exact_LiteralNumericSamePoolLeastEdge (edge s ctx ty) (vertices s a) a b
    hs (same ▸ ht) ab ba

#print axioms exact_LiteralNumericSamePoolLeastEdge
#print axioms exact_LiteralNumericLeastEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericLeastEdgeProof
