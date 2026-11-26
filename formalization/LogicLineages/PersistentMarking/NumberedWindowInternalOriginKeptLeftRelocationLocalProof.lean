module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsShiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationLocalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (consBackward)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalLiteralCountAppendAgreementProof (exact_LiteralCommonPrefixCongruence)
open NumberedWindowInternalLiteralCountConsAgreementProof (exact_LiteralConsCongruence)
open NumberedWindowInternalLiteralCountConsShiftProof (exact_LiteralConsShift)
open NumberedWindowInternalOriginKeptSplitTargets (piece)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev App (l r out : OTerm α) : Formula α := programGraph append out ![l,r]
abbrev Cmp (l r : OTerm α) : Formula α := programGraph permutation (suc z) ![l,r]

/-- Move exactly one left-assigned removed occurrence in the original
left source allocation. The two new actual append reports are held. -/
theorem exact_OriginalKeptLeftSource (left head lk lr short long lkNew oldJoin middle newJoin : OTerm α)
    (old : Nonempty (Derivation B Γ (piece left lk lr oldJoin)))
    (selected : Nonempty (Derivation B Γ (Cmp lr long)))
    (removedCell : Nonempty (Derivation B Γ (consGraph long head short)))
    (keptCell : Nonempty (Derivation B Γ (consGraph lkNew head lk)))
    (mid : Nonempty (Derivation B Γ (App lk long middle)))
    (new : Nonempty (Derivation B Γ (App lkNew short newJoin))) :
    Nonempty (Derivation B Γ (piece left lkNew short newJoin)) := by
  obtain ⟨p⟩ := old
  have first := exact_LiteralCommonPrefixCongruence lk lr long oldJoin middle
    ⟨Derivation.conjunctionLeft p⟩ mid selected
  have second := exact_LiteralConsShift head lk short lkNew long newJoin middle
    keptCell removedCell new mid
  have reverse := NumberedWindowInternalLiteralCountEquivalenceProof.exact_LiteralObserverSymmetry
    newJoin middle second
  have same := exact_LiteralObserverTransitivity left oldJoin newJoin
    ⟨Derivation.conjunctionRight p⟩ (exact_LiteralObserverTransitivity oldJoin middle newJoin first reverse)
  obtain ⟨a⟩ := new
  obtain ⟨b⟩ := same
  exact ⟨Derivation.conjunctionIntroduction a b⟩

/-- Extend the original kept allocation using the literal same head at
the target and left allocation; actual append is reconstructed. -/
theorem exact_OriginalKeptLeftKeep (tail head kept lk rk lkNew joined newJoin : OTerm α)
    (old : Nonempty (Derivation B Γ (piece tail lk rk joined)))
    (keptCell : Nonempty (Derivation B Γ (consGraph kept head tail)))
    (leftCell : Nonempty (Derivation B Γ (consGraph lkNew head lk)))
    (joinCell : Nonempty (Derivation B Γ (consGraph newJoin head joined))) :
    Nonempty (Derivation B Γ (piece kept lkNew rk newJoin)) := by
  obtain ⟨p⟩ := old
  have app : Nonempty (Derivation B Γ (App lkNew rk newJoin)) :=
    consBackward lkNew head lk rk joined newJoin leftCell ⟨Derivation.conjunctionLeft p⟩ joinCell
  have cmp := exact_LiteralConsCongruence head tail joined kept newJoin
    keptCell joinCell ⟨Derivation.conjunctionRight p⟩
  obtain ⟨a⟩ := app
  obtain ⟨b⟩ := cmp
  exact ⟨Derivation.conjunctionIntroduction a b⟩

#print axioms exact_OriginalKeptLeftSource
#print axioms exact_OriginalKeptLeftKeep
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationLocalProof
