module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseExistenceProof
public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityProof

@[expose] public section

/-! Assembly: `TowerHypotheses` for the paper's actual collapse data, outright, and the first
equality of `lem:tower-cofinality` for it via #1463. -/

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open NativeTowerSequenceTargets
open scoped Ordinal

theorem actualTowerHypotheses : ActualTowerHypotheses := by
  intro Z s add mul w one pow fix h1 h2
  obtain ⟨infl, hΓ⟩ := veblenInflationary Z s add mul w one pow fix h1 h2
  obtain ⟨aboveOne, _, _, supClosed⟩ := criticalFacts _ _ infl hΓ
  exact {
    characterization := actualCharacterization _ _ infl hΓ
    increasing := fun n => show argument n < argument (n+1) from exact_StrictlyIncreasing (Nat.lt_succ_self n)
    below := fun n => show argument n < endpoint from exact_BelowEndpoint n
    cofinal := fun η hη => (exact_Cofinal η.val).1 hη
    normBound := fun n => normBound n
    criticalAboveOne := aboveOne
    criticalSup := supClosed }

theorem actualTowerSupremum : ActualTowerSupremum := by
  intro Z s add mul w one pow fix h1 h2
  have tower := actualTowerHypotheses Z s add mul w one pow fix h1 h2
  exact conditionalTowerSupremum ActualIndex Ordinal.{0} (veblenData fix pow w) tower _
    (isLUB_ciSup (Ordinal.bddAbove_range _))

#print axioms normBound
#print axioms normCountable
#print axioms criticalFacts
#print axioms veblenInflationary
#print axioms actualCharacterization
#print axioms actualTowerHypotheses
#print axioms actualTowerSupremum

end LogicLineages.PersistentMarking.ActualCollapse
