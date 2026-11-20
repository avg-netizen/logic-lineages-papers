module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationExchangeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationRoundsProof
open NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicApplicationExchangeProof (scalarExchange)
open NumberedWindowClassAlgorithm (advance rounds)
open NumberedWindowScalarAlgorithm (Settings edge least vertices)

private theorem advanceHit {E : Nat → Nat → Bool} {pool reached : List Nat} {q : Nat}
    (h : q ∈ advance E pool reached) : ∃ p, p ∈ reached ∧ (p = q ∨ E p q = true) := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  exact h.2

private theorem forward (s : Settings) (Γ : List Nat) (requested dom cod fn arg : Nat)
    (atom : AtomHead fn) (pool : List Nat) (fuel q : Nat)
    (h : q ∈ rounds (edge s Γ requested) pool (auxRaw dom cod fn arg) fuel) :
    ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads arg a := by
  induction fuel generalizing q with
  | zero =>
    simp only [rounds,List.mem_filter,beq_iff_eq] at h
    exact ⟨arg,h.2.symm,ArgumentMoves.empty arg⟩
  | succ fuel ih =>
    change q ∈ advance (edge s Γ requested) pool
      (rounds (edge s Γ requested) pool (auxRaw dom cod fn arg) fuel) at h
    obtain ⟨prior,hPrior,step⟩ := advanceHit h
    obtain ⟨a,priorCode,trace⟩ := ih prior hPrior
    rcases step with same | moved
    · exact ⟨a,same.symm.trans priorCode,trace⟩
    · rw [priorCode] at moved
      obtain ⟨b,code,child,_⟩ := (scalarExchange s Γ requested dom cod fn a q atom).1 moved
      exact ⟨b,code,trace.snoc child⟩

private theorem backward (s : Settings) (Γ : List Nat) (requested dom cod fn : Nat)
    (atom : AtomHead fn) (pool : List Nat) (fuel q arg : Nat)
    (h : auxRaw dom cod fn arg ∈ rounds (edge s Γ requested) pool q fuel) :
    ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads a arg := by
  induction fuel generalizing arg with
  | zero =>
    simp only [rounds,List.mem_filter,beq_iff_eq] at h
    exact ⟨arg,h.2,ArgumentMoves.empty arg⟩
  | succ fuel ih =>
    change auxRaw dom cod fn arg ∈ advance (edge s Γ requested) pool
      (rounds (edge s Γ requested) pool q fuel) at h
    obtain ⟨prior,hPrior,step⟩ := advanceHit h
    rcases step with same | moved
    · rw [same] at hPrior
      exact ih arg hPrior
    · obtain ⟨b,priorCode,child,_⟩ :=
        (scalarExchange s Γ requested dom cod fn arg prior atom).2 moved
      rw [priorCode] at hPrior
      obtain ⟨a,code,trace⟩ := ih b hPrior
      exact ⟨a,code,trace.snoc child⟩

theorem finiteRounds : ExactAtomicAuxFiniteRounds := by
  intro s Γ requested dom cod fn arg atom pool fuel q
  exact ⟨forward s Γ requested dom cod fn arg atom pool fuel q,
    backward s Γ requested dom cod fn atom pool fuel q arg⟩

theorem atomicLeast : ExactAtomicAuxLeast := by
  intro s Γ requested dom cod fn arg q atom
  constructor
  · intro h
    let pool := vertices s (auxRaw dom cod fn arg)
    change (rounds (edge s Γ requested) pool (auxRaw dom cod fn arg) pool.length).min? = some q at h
    exact (finiteRounds s Γ requested dom cod fn arg atom pool pool.length q).1
      (List.min?_eq_some_iff.mp h).1
  · intro h
    let pool := vertices s q
    change (rounds (edge s Γ requested) pool q pool.length).min? = some (auxRaw dom cod fn arg) at h
    exact (finiteRounds s Γ requested dom cod fn arg atom pool pool.length q).2
      (List.min?_eq_some_iff.mp h).1

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationRoundsProof
