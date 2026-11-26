module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseAddressPositive

abbrev args {α : Type} (left cert right : OTerm α) : Fin 3 → OTerm α := ![left,cert,right]

theorem acceptedRename {α β : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) (j : α → β) :
    (programGraph (addressPositive cv tv raw least) (suc z) (args left cert right)).relabel j =
      programGraph (addressPositive cv tv raw least) (suc z) (args (left.relabel j) (cert.relabel j) (right.relabel j)) := by
  rw [graph3Rename,sucRelabel,zRelabel]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem slotIntro (p : Program 1) (slot : Fin 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (observed : Nonempty (Derivation body Γ (unary p out (xs slot)))) :
    Nonempty (Derivation body Γ (programGraph (atAddress p slot) out xs)) := by
  unfold atAddress
  apply compositionValue p (fun _ : Fin 1 => .projection slot) out xs (![xs slot] : Fin 1 → OTerm α) observed
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue slot xs

theorem slotRead (p : Program 1) (slot : Fin 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (known : Nonempty (Derivation body Γ (programGraph (atAddress p slot) out xs))) :
    Nonempty (Derivation body Γ (unary p out (xs slot))) := by
  apply compositionRecover p (fun _ : Fin 1 => .projection slot) out xs (![xs slot] : Fin 1 → OTerm α) known
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue slot xs

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
