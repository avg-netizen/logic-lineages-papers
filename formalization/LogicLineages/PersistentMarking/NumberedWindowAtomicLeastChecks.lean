module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastRoundsProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
open NumberedWindowAtomicRawStep NumberedWindowAtomicLeastTargets
open NumberedWindowAtomicLeastExchangeProof (exchangeRows scalarIsolation)
open NumberedWindowAtomicLeastRoundsProof (roundSingleton)
open NumberedWindowScalarAlgorithm (Settings edge vertices least)
open NumberedWindowClassAlgorithm (rounds)

private theorem leastOfRounds (s : Settings) (Γ : List Nat) (requested atom : Nat)
    (seen : RoundSingleton s Γ requested atom) : LeastSingleton s Γ requested atom := by
  constructor
  · intro q found
    let pool := vertices s q
    change (rounds (edge s Γ requested) pool q pool.length).min? = some atom at found
    exact (seen pool pool.length q atom).1 (List.min?_eq_some_iff.mp found).1
  · intro y found
    let pool := vertices s atom
    change (rounds (edge s Γ requested) pool atom pool.length).min? = some y at found
    exact (seen pool pool.length atom y).2 (List.min?_eq_some_iff.mp found).1

theorem exact_AtomicExchangeRows : ExactAtomicExchangeRows := exchangeRows

theorem exact_AtomicScalarEdgeIsolation : ExactAtomicScalarEdgeIsolation := scalarIsolation

theorem exact_AtomicRoundSingleton : ExactAtomicRoundSingleton := roundSingleton

theorem exact_AtomicLeastSingleton : ExactAtomicLeastSingleton := by
  intro s Γ requested t
  have h := roundSingleton s Γ requested t
  exact ⟨fun n => leastOfRounds s Γ requested (freeRaw t n) (h.1 n),
    leastOfRounds s Γ requested (bottomRaw t) h.2⟩

#print axioms exact_AtomicExchangeRows
#print axioms exact_AtomicScalarEdgeIsolation
#print axioms exact_AtomicRoundSingleton
#print axioms exact_AtomicLeastSingleton
end LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
