import LogicLineages.PersistentMarking.UnaryTransportStep
namespace LogicLineages.PersistentMarking.UnaryTransportProof
open Spine UnaryTransportResults ExtendedMeasure

theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j :=
  Nat.strongRecOn (motive := fun n => ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j) n
    (fun n ih j h hn => step S n (fun j' h' hlt => ih (treeSize h') hlt j' h' rfl) j h hn)

theorem unaryTransport : ApplicationCovarianceTargets.UnaryTransport := by
  intro S q s a b τ r h hab hqa hsb hright
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl a b τ r hab hqa hsb hright
end LogicLineages.PersistentMarking.UnaryTransportProof
