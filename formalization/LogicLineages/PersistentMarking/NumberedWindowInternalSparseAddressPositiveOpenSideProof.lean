module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary takeUnary)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotIntro slotRead)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem sideRead (cv tv : Program 1) (slot : Fin 3) (xs : Fin 3 → OTerm α) (c t k : OTerm α)
    (good : Nonempty (Derivation body Γ (programGraph (sideGood cv tv slot) (suc z) xs)))
    (ct : Nonempty (Derivation body Γ (programGraph (atAddress rawContext slot) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult slot) t xs)))
    (cl : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast slot) k xs))) :
    Nonempty (Derivation body Γ (addressReport (xs slot) c t k)) ∧
      Nonempty (Derivation body Γ (unary cv (suc z) c)) ∧
      Nonempty (Derivation body Γ (unary tv (suc z) t)) := by
  let P := atAddress (applyUnary cv rawContext) slot
  let Q := atAddress (applyUnary tv rawResult) slot
  obtain ⟨h⟩ := conjunctionRecover (atAddress addressGood slot) (conjunction P Q) xs good
  obtain ⟨b⟩ := conjunctionRecover P Q xs ⟨Derivation.conjunctionRight h⟩
  obtain ⟨shell⟩ := slotRead addressGood slot (suc z) xs ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨c'⟩ := slotRead rawContext slot c xs ct
  obtain ⟨t'⟩ := slotRead rawResult slot t xs ty
  obtain ⟨k'⟩ := slotRead rawLeast slot k xs cl
  have complete : Derivation body Γ (addressReport (xs slot) c t k) :=
    Derivation.conjunctionIntroduction shell (Derivation.conjunctionIntroduction c'
      (Derivation.conjunctionIntroduction t' k'))
  have atC := slotRead (applyUnary cv rawContext) slot (suc z) xs ⟨Derivation.conjunctionLeft b⟩
  have atT := slotRead (applyUnary tv rawResult) slot (suc z) xs ⟨Derivation.conjunctionRight b⟩
  exact ⟨⟨complete⟩,takeUnary cv rawContext (suc z) (xs slot) c atC ⟨c'⟩,
    takeUnary tv rawResult (suc z) (xs slot) t atT ⟨t'⟩⟩

theorem sideIntro (cv tv : Program 1) (slot : Fin 3) (xs : Fin 3 → OTerm α) (c t k : OTerm α)
    (fields : Nonempty (Derivation body Γ (addressReport (xs slot) c t k)))
    (ctxOk : Nonempty (Derivation body Γ (unary cv (suc z) c)))
    (tyOK : Nonempty (Derivation body Γ (unary tv (suc z) t))) :
    Nonempty (Derivation body Γ (programGraph (sideGood cv tv slot) (suc z) xs)) := by
  obtain ⟨f⟩ := fields
  let out := suc (z : OTerm α)
  let P := atAddress (applyUnary cv rawContext) slot
  let Q := atAddress (applyUnary tv rawResult) slot
  have a := makeUnary cv rawContext out (xs slot) c ctxOk
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight f)⟩
  have b := makeUnary tv rawResult out (xs slot) t tyOK
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight f))⟩
  exact conjunctionAccept (atAddress addressGood slot) (conjunction P Q) xs
    (slotIntro addressGood slot out xs ⟨Derivation.conjunctionLeft f⟩)
    (conjunctionAccept P Q xs (slotIntro (applyUnary cv rawContext) slot out xs a)
      (slotIntro (applyUnary tv rawResult) slot out xs b))

theorem align (n fromC fromT c t cls : OTerm α)
    (ce : Nonempty (Derivation body Γ (eqn fromC c)))
    (te : Nonempty (Derivation body Γ (eqn fromT t)))
    (old : Nonempty (Derivation body Γ (addressReport n fromC fromT cls))) :
    Nonempty (Derivation body Γ (addressReport n c t cls)) := by
  obtain ⟨o⟩ := old
  obtain ⟨a⟩ := outputTransport rawContext fromC c (![n] : Fin 1 → OTerm α) ce
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight o)⟩
  obtain ⟨b⟩ := outputTransport rawResult fromT t (![n] : Fin 1 → OTerm α) te
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight o))⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft o)
    (Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight o)))))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
