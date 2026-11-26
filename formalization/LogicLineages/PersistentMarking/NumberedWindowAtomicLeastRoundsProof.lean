module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastExchangeProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicLeastRoundsProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicLeastTargets
open NumberedWindowAtomicLeastExchangeProof (scalarIsolation)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowClassAlgorithm (advance rounds)

private theorem advanceHit {E : Nat → Nat → Bool} {pool reached : List Nat} {v : Nat}
    (h : v ∈ advance E pool reached) : ∃ w, w ∈ reached ∧ (w = v ∨ E w v = true) := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  exact h.2

private theorem startsFrom {E : Nat → Nat → Bool} {pool : List Nat} {atom seed : Nat}
    (noIn : ∀ w, E w atom = false) (fuel : Nat)
    (h : atom ∈ rounds E pool seed fuel) : seed = atom := by
  induction fuel with
  | zero =>
    simp only [rounds,List.mem_filter,beq_iff_eq] at h
    exact h.2
  | succ fuel ih =>
    change atom ∈ advance E pool (rounds E pool seed fuel) at h
    obtain ⟨w,prior,step⟩ := advanceHit h
    rcases step with eq | hit
    · subst w
      exact ih prior
    · rw [noIn w] at hit
      cases hit

private theorem reachesOnly {E : Nat → Nat → Bool} {pool : List Nat} {atom : Nat}
    (noOut : ∀ w, E atom w = false) (fuel out : Nat)
    (h : out ∈ rounds E pool atom fuel) : out = atom := by
  induction fuel generalizing out with
  | zero =>
    simp only [rounds,List.mem_filter,beq_iff_eq] at h
    exact h.2.symm
  | succ fuel ih =>
    change out ∈ advance E pool (rounds E pool atom fuel) at h
    obtain ⟨w,prior,step⟩ := advanceHit h
    have same := ih w prior
    subst w
    rcases step with eq | hit
    · exact eq.symm
    · rw [noOut out] at hit
      cases hit

private theorem singleton (s : Settings) (Γ : List Nat) (requested atom : Nat)
    (isolation : Isolated s Γ requested atom) : RoundSingleton s Γ requested atom := by
  intro pool fuel seed out
  exact ⟨startsFrom (fun w => (isolation w).2) fuel,
    reachesOnly (fun w => (isolation w).1) fuel out⟩

theorem roundSingleton : ExactAtomicRoundSingleton := by
  intro s Γ requested t
  have h := scalarIsolation s Γ requested t
  exact ⟨fun n => singleton s Γ requested (freeRaw t n) (h.1 n),
    singleton s Γ requested (bottomRaw t) h.2⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicLeastRoundsProof
