module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotIntro)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalParameterizedAddressPositive (addressAt)
open NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof (gateRead foldRead)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Read the actual physical fold on the exact already-audited address
fields. Neither a new endpoint nor a new representative is chosen. -/
theorem exact_OpenAddressAtKnownFold (cv tv : Program 1) (P : Program 5)
    (x w y c t src dst : OTerm α)
    (left : Nonempty (Derivation B Γ (addressReport x c t src)))
    (right : Nonempty (Derivation B Γ (addressReport y c t dst)))
    (held : Nonempty (Derivation B Γ (programGraph (addressAt cv tv P) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (programGraph P (suc z) ![c,t,src,w,dst])) := by
  let xs : Fin 3 → OTerm α := ![x,w,y]
  obtain ⟨a⟩ := left
  obtain ⟨b⟩ := right
  obtain ⟨_,_,_,_,body⟩ := gateRead cv tv P xs held
  have ctx := slotIntro rawContext 0 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight a)⟩
  have ty := slotIntro rawResult 0 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight a))⟩
  have fr := slotIntro rawLeast 0 src xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight a))⟩
  have dstRead := slotIntro rawLeast 2 dst xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight b))⟩
  exact foldRead P xs c t src dst ctx ty fr dstRead body

#print axioms exact_OpenAddressAtKnownFold
end LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
