module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSuffixProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppendListProof (consBackward)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalLiteralCountAppendSuffixProof (exact_LiteralCommonSuffixCongruence)
open NumberedWindowInternalLiteralCountConsAgreementProof (exact_LiteralConsCancellation)
open NumberedWindowInternalOriginKeptSplitTargets (piece evidence)
open NumberedWindowInternalOriginKeptLeftRelocationLocalProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Cancel the same concrete head from the removed target and its
count-equivalent actual join after replacing the left removed row. -/
theorem exact_OriginalKeptLeftRemove (removed head extra lr rr short long joined shortJoin longJoin : OTerm α)
    (old : Nonempty (Derivation B Γ (piece extra lr rr joined)))
    (selected : Nonempty (Derivation B Γ (Cmp lr long)))
    (outerCell : Nonempty (Derivation B Γ (consGraph extra head removed)))
    (leftCell : Nonempty (Derivation B Γ (consGraph long head short)))
    (joinCell : Nonempty (Derivation B Γ (consGraph longJoin head shortJoin)))
    (shortApp : Nonempty (Derivation B Γ (App short rr shortJoin))) :
    Nonempty (Derivation B Γ (piece removed short rr shortJoin)) := by
  obtain ⟨p⟩ := old
  have longApp : Nonempty (Derivation B Γ (App long rr longJoin)) :=
    consBackward long head short rr shortJoin longJoin leftCell shortApp joinCell
  have same := exact_LiteralCommonSuffixCongruence lr long rr joined longJoin
    ⟨Derivation.conjunctionLeft p⟩ longApp selected
  have joinedCmp := exact_LiteralObserverTransitivity extra joined longJoin
    ⟨Derivation.conjunctionRight p⟩ same
  have cmp := exact_LiteralConsCancellation head removed shortJoin extra longJoin
    outerCell joinCell joinedCmp
  obtain ⟨a⟩ := shortApp
  obtain ⟨b⟩ := cmp
  exact ⟨Derivation.conjunctionIntroduction a b⟩

/-- Update only the three affected reports of the eight physical
witnesses. The right source report is reused verbatim. Selection,
actual new cons/append outputs, and later existential packaging are separate. -/
theorem exact_OriginalKeptSplitRelocateLeft
    (left right kt removed kept extra head short long lkNew mid sourceNew keepNew removeNew removeLift : OTerm α)
    (w : Fin 8 → OTerm α)
    (old : Nonempty (Derivation B Γ (evidence left right kt extra w)))
    (selected : Nonempty (Derivation B Γ (Cmp (w 1) long)))
    (parentKeep : Nonempty (Derivation B Γ (consGraph kept head kt)))
    (parentRemove : Nonempty (Derivation B Γ (consGraph extra head removed)))
    (leftRemove : Nonempty (Derivation B Γ (consGraph long head short)))
    (leftKeep : Nonempty (Derivation B Γ (consGraph lkNew head (w 0))))
    (sourceMid : Nonempty (Derivation B Γ (App (w 0) long mid)))
    (sourceApp : Nonempty (Derivation B Γ (App lkNew short sourceNew)))
    (keptJoin : Nonempty (Derivation B Γ (consGraph keepNew head (w 6))))
    (removedApp : Nonempty (Derivation B Γ (App short (w 3) removeNew)))
    (removedJoin : Nonempty (Derivation B Γ (consGraph removeLift head removeNew))) :
    Nonempty (Derivation B Γ (evidence left right kept removed
      ![lkNew,short,w 2,w 3,sourceNew,w 5,keepNew,removeNew])) := by
  obtain ⟨old⟩ := old
  let rest := Derivation.conjunctionRight old
  let tails := Derivation.conjunctionRight rest
  obtain ⟨leftNew⟩ := exact_OriginalKeptLeftSource left head (w 0) (w 1) short long lkNew (w 4) mid sourceNew
    ⟨Derivation.conjunctionLeft old⟩ selected leftRemove leftKeep sourceMid sourceApp
  obtain ⟨keepNext⟩ := exact_OriginalKeptLeftKeep kt head kept (w 0) (w 2) lkNew (w 6) keepNew
    ⟨Derivation.conjunctionLeft tails⟩ parentKeep leftKeep keptJoin
  obtain ⟨removeNext⟩ := exact_OriginalKeptLeftRemove removed head extra (w 1) (w 3) short long (w 7)
    removeNew removeLift ⟨Derivation.conjunctionRight tails⟩ selected parentRemove leftRemove
    removedJoin removedApp
  exact ⟨Derivation.conjunctionIntroduction leftNew
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft rest)
      (Derivation.conjunctionIntroduction keepNext removeNext))⟩

#print axioms exact_OriginalKeptLeftRemove
#print axioms exact_OriginalKeptSplitRelocateLeft
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationProof
