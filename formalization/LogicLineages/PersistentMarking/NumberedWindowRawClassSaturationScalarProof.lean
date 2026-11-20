module
public import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationTargets
import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationClassProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationScalarProof
open NumberedWindowClassAlgorithm (rounds members)
open NumberedWindowScalarAlgorithm (Settings edge admitted vertices least)
open NumberedWindowRawClassSaturationTargets
open NumberedWindowRawClassSaturationClassProof (roundsProperty exactSamePool)

private theorem selectedMember (s : Settings) (ctx : List Nat) (requested seed y : Nat)
    (found : least s ctx requested seed = some y) :
    y ∈ members (edge s ctx requested) (vertices s seed) seed :=
  (List.min?_eq_some_iff.mp found).1

theorem admittedResult : ExactRawLeastResultAdmitted := by
  intro s ctx requested seed y seedOK found
  apply roundsProperty (edge s ctx requested) (vertices s seed) seed
    (fun a => admitted s ctx requested a = true) seedOK _ (vertices s seed).length y
    (selectedMember s ctx requested seed y found)
  intro a b _ checked
  have guards :
      (NumberedWindowExchangeAlgorithm.bits s.equivalentHeads a b).1 = true ∧
        admitted s ctx requested a = true ∧ admitted s ctx requested b = true := by
    simpa only [edge,Bool.and_eq_true,and_assoc] using checked
  exact guards.2.2

theorem closureWithVertices : ExactRawLeastClosureWithVertices := by
  intro s ctx requested sameVertices seed y seedOK found
  let test := edge s ctx requested
  let pool := vertices s seed
  have same : vertices s y = pool := by
    apply roundsProperty test pool seed (fun z => vertices s z = pool) rfl _ pool.length y
      (selectedMember s ctx requested seed y found)
    intro a b before via
    exact (sameVertices a b via).trans before
  have ownPool := exactSamePool test pool seed y found
  refine ⟨same,admittedResult s ctx requested seed y seedOK found,?_⟩
  change NumberedWindowClassAlgorithm.least test (vertices s y) y = some y
  rw [same]
  exact ownPool

end LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationScalarProof
