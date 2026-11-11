module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelChildBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalTypedDecoderStepSpecification
open InternalPairingSumBounds InternalPairingSumBoundsProof InternalPairingSumBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalOriginalPairingOrderArithmeticProof
open InternalUnpairReverseBoundsArithmeticProof InternalRecursionClosureLogicProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairSum (code left right : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepPair code left right))) :
    Nonempty (Derivation body Delta (weakBound (add left right) code)) :=
  closedApply (actualOriginalPairingSumBound body alpha code left right) h

theorem pairRightBound (code left right : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepPair code left right))) :
    Nonempty (Derivation body Delta (weakBound right code)) :=
  weakTrans right (add left right) code (rightWeakAdd left right) (pairSum code left right h)

/-- Any positive original tag pays the one request-opening successor. -/
theorem taggedOneBound (raw payload spare child : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (suc spare) payload)))
    (hc : Nonempty (Derivation body Delta (weakBound child payload))) :
    Nonempty (Derivation body Delta (weakBound (suc child) raw)) := by
  have hlow := weakTrans child payload (add spare payload) hc (rightWeakAdd spare payload)
  have hs := successorWeak child (add spare payload) hlow
  have htag := weakTransport (suc child) (add (suc spare) payload)
    (suc child) (suc (add spare payload)) ⟨refl (suc child)⟩ ⟨leftSuccessor spare payload⟩ hs
  exact weakTrans (suc child) (add (suc spare) payload) raw htag
    (pairSum raw (suc spare) payload hp)

/-- Tags at least two pay both child successors, before any suffix weight. -/
theorem taggedTwoBound (raw payload spare first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (suc (suc spare)) payload)))
    (hc : Nonempty (Derivation body Delta (weakBound (add first second) payload))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  have hlow := weakTrans (add first second) payload (add spare payload) hc (rightWeakAdd spare payload)
  have hs := successorWeak (suc (add first second)) (suc (add spare payload))
    (successorWeak (add first second) (add spare payload) hlow)
  have ec : Derivation body Delta (eqn (childFuelSum first second) (suc (suc (add first second)))) :=
    trans (leftSuccessor first (suc second)) (congSuc (addSucc first second))
  have et : Derivation body Delta
      (eqn (add (suc (suc spare)) payload) (suc (suc (add spare payload)))) :=
    trans (leftSuccessor (suc spare) payload) (congSuc (leftSuccessor spare payload))
  have htag := weakTransport (childFuelSum first second) (add (suc (suc spare)) payload)
    (suc (suc (add first second))) (suc (suc (add spare payload))) ⟨ec⟩ ⟨et⟩ hs
  exact weakTrans (childFuelSum first second) (add (suc (suc spare)) payload) raw htag
    (pairSum raw (suc (suc spare)) payload hp)

theorem lambdaBound (raw payload domain child : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 1) payload)))
    (hc : Nonempty (Derivation body Delta (StepPair payload domain child))) :
    Nonempty (Derivation body Delta (weakBound (suc child) raw)) :=
  taggedOneBound raw payload z child hp (pairRightBound payload domain child hc)

theorem applicationBound (raw payload children domain first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 2) payload)))
    (hm : Nonempty (Derivation body Delta (StepPair payload domain children)))
    (hc : Nonempty (Derivation body Delta (StepPair children first second))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) :=
  taggedTwoBound raw payload z first second hp
    (weakTrans (add first second) children payload (pairSum children first second hc)
      (pairRightBound payload domain children hm))

theorem ordinaryBound (raw payload head base : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 4) payload)))
    (hc : Nonempty (Derivation body Delta (StepPair payload head base))) :
    Nonempty (Derivation body Delta (weakBound (suc base) raw)) :=
  taggedOneBound raw payload (numeral 3) base hp (pairRightBound payload head base hc)

/-- Follow every actual numbered payload pair. Neither the recorded type,
head, label nor extra type-list contributes to the request work measure. -/
theorem numberedBound (raw payload a b c d label head typ base types extras : OTerm alpha)
    (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Delta (StepPair payload label a)))
    (h2 : Nonempty (Derivation body Delta (StepPair a head b)))
    (h3 : Nonempty (Derivation body Delta (StepPair b typ c)))
    (h4 : Nonempty (Derivation body Delta (StepPair c base d)))
    (h5 : Nonempty (Derivation body Delta (StepPair d types extras))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum base extras) raw)) := by
  have he := addWeakLeft base extras d (pairRightBound d types extras h5)
  have hc := weakTrans (add base extras) (add base d) c he (pairSum c base d h4)
  have hb := weakTrans (add base extras) c b hc (pairRightBound b typ c h3)
  have ha := weakTrans (add base extras) b a hb (pairRightBound a head b h2)
  have hp := weakTrans (add base extras) a payload ha (pairRightBound payload label a h1)
  exact taggedTwoBound raw payload (numeral 3) base extras h0 hp

theorem consBound (raw payload children domain first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
    (hm : Nonempty (Derivation body Delta (StepPair payload domain children)))
    (hc : Nonempty (Derivation body Delta (StepPair children first second))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) :=
  taggedTwoBound raw payload (numeral 5) first second hp
    (weakTrans (add first second) children payload (pairSum children first second hc)
      (pairRightBound payload domain children hm))

theorem actualOriginalTypedInternalChildFuelBounds :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalChildFuelBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro body alpha raw payload domain child
    let A := StepPair raw (numeral 1) payload ⊓ StepPair payload domain child
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := lambdaBound raw payload domain child (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩
  · intro body alpha raw payload children domain first second
    let A := StepPair raw (numeral 2) payload ⊓
      (StepPair payload domain children ⊓ StepPair children first second)
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := applicationBound raw payload children domain first second
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    exact ⟨Derivation.implicationIntroduction d⟩
  · intro body alpha raw payload head base
    let A := StepPair raw (numeral 4) payload ⊓ StepPair payload head base
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := ordinaryBound raw payload head base (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩
  · intro body alpha raw payload a b c d label head typ base types extras
    let A := StepPair raw (numeral 5) payload ⊓ (StepPair payload label a ⊓
      (StepPair a head b ⊓ (StepPair b typ c ⊓ (StepPair c base d ⊓ StepPair d types extras))))
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨proof⟩ := numberedBound raw payload a b c d label head typ base types extras
      (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
      (andLeft (andRight (andRight (andRight h))))
      (andLeft (andRight (andRight (andRight (andRight h)))))
      (andRight (andRight (andRight (andRight (andRight h)))))
    exact ⟨Derivation.implicationIntroduction proof⟩
  · intro body alpha raw payload children domain first second
    let A := StepPair raw (numeral 7) payload ⊓
      (StepPair payload domain children ⊓ StepPair children first second)
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := consBound raw payload children domain first second
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelChildBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelChildBoundsProof
