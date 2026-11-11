module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalPairingSumBounds InternalPairingSumBoundsProof InternalPairingSumBoundsArithmeticProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalQuotientComparisonProof (equalToNext)
open InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalAdditionLawsProof InternalRecursionClosureLogicProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem weakRename {beta : Type} (s t : OTerm alpha) (j : alpha → beta) :
    (weakBound s t).relabel j = weakBound (s.relabel j) (t.relabel j) := by
  change (ltF s (suc t)).relabel j = ltF _ (suc _)
  simp only [orderRename,sucRelabel]

/-- Pair sums are bounded in the original object arithmetic. -/
theorem pairSum (raw x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw x y))) :
    Nonempty (Derivation body Delta (weakBound (add x y) raw)) :=
  closedApply (actualOriginalPairingSumBound body alpha raw x y) hp

theorem leftBound (raw x : OTerm alpha)
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.left x raw))) :
    Nonempty (Derivation body Delta (weakBound x raw)) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Theta y hj hy
  rw [weakRename]
  simp only [consTermRename,emptyRename] at hy
  have hx' := renameInto hx j Theta hj
  rw [graph1Rename] at hx'
  exact weakTrans (x.relabel j) (add (x.relabel j) y) (raw.relabel j)
    (leftWeakAdd (x.relabel j) y)
    (pairSum (raw.relabel j) (x.relabel j) y
      (reconstructPair (raw.relabel j) (x.relabel j) y hx' hy))

theorem rightBound (raw y : OTerm alpha)
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y raw))) :
    Nonempty (Derivation body Delta (weakBound y raw)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta x hj hx
  rw [weakRename]
  simp only [consTermRename,emptyRename] at hx
  have hy' := renameInto hy j Theta hj
  rw [graph1Rename] at hy'
  exact weakTrans (y.relabel j) (add x (y.relabel j)) (raw.relabel j)
    (rightWeakAdd x (y.relabel j))
    (pairSum (raw.relabel j) x (y.relabel j)
      (reconstructPair (raw.relabel j) x (y.relabel j) hx hy'))

/-- Any finite selector path is weakly bounded by its original raw input.
This is an internal graph proof, not a standard-natural unpair estimate. -/
theorem pathBound {n : Nat} (path : List Bool) (query : Program n)
    (raw out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hp : Nonempty (Derivation body Delta (programGraph (pathQuery path query) out xs))) :
    Nonempty (Derivation body Delta (weakBound out raw)) := by
  induction path generalizing alpha query with
  | nil =>
    obtain ⟨he⟩ := valueUnique query out raw xs hp hq
    exact ⟨equalToNext he⟩
  | cons direction rest ih =>
    cases direction with
    | false =>
      apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
      intro beta j Theta middle hj hm
      rw [weakRename]
      simp only [consTermRename,emptyRename] at hm
      have hq' := renameInto hq j Theta hj
      have hp' := renameInto hp j Theta hj
      simp only [programRename] at hq' hp'
      have hmid := unaryValue InternalUnpair.left query middle (raw.relabel j)
        (fun i => (xs i).relabel j) hm hq'
      exact weakTrans (out.relabel j) middle (raw.relabel j)
        (ih (leftOf query) middle (out.relabel j) (fun i => (xs i).relabel j) hmid hp')
        (leftBound (raw.relabel j) middle hm)
    | true =>
      apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
      intro beta j Theta middle hj hm
      rw [weakRename]
      simp only [consTermRename,emptyRename] at hm
      have hq' := renameInto hq j Theta hj
      have hp' := renameInto hp j Theta hj
      simp only [programRename] at hq' hp'
      have hmid := unaryValue InternalUnpair.right query middle (raw.relabel j)
        (fun i => (xs i).relabel j) hm hq'
      exact weakTrans (out.relabel j) middle (raw.relabel j)
        (ih (rightOf query) middle (out.relabel j) (fun i => (xs i).relabel j) hmid hp')
        (rightBound (raw.relabel j) middle hm)

theorem numeralWeak (m n : Nat) (h : m ≤ n) :
    Nonempty (Derivation body Delta (weakBound (numeral m : OTerm alpha) (numeral n))) := by
  induction h with
  | refl => exact ⟨equalToNext (refl (numeral m))⟩
  | @step n _ ih => exact rightSuccessor (numeral m) (suc (numeral n)) ih

/-- Positive literal tags pay for the opening and return of a unary node. -/
theorem taggedUnaryBound (tag : Nat) (htag : 1 ≤ tag) (raw payload child : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag) payload)))
    (hc : Nonempty (Derivation body Delta (weakBound child payload))) :
    Nonempty (Derivation body Delta (weakBound (suc child) raw)) := by
  have h1 := addWeakRight (body := body) (Gamma := Delta) (numeral 1) (numeral tag) child (numeralWeak 1 tag htag)
  have h2 := addWeakLeft (numeral tag) child payload hc
  obtain ⟨h⟩ := weakTrans (add (numeral 1) child) (add (numeral tag) payload) raw
    (weakTrans _ _ _ h1 h2) (pairSum raw (numeral tag) payload hp)
  have he : Derivation body Delta (eqn (add (numeral 1) child) (suc child)) :=
    trans (leftSuccessor z child) (congSuc (leftZero child))
  exact ⟨orderLeft (suc raw) he h⟩

/-- Tags at least two pay for both child traversals and both surrounding steps. -/
theorem taggedBinaryBound (tag : Nat) (htag : 2 ≤ tag) (raw payload first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag) payload)))
    (hc : Nonempty (Derivation body Delta (weakBound (add first second) payload))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  have h1 := addWeakRight (body := body) (Gamma := Delta) (numeral 2) (numeral tag) (add first second) (numeralWeak 2 tag htag)
  have h2 := addWeakLeft (numeral tag) (add first second) payload hc
  obtain ⟨h⟩ := weakTrans (add (numeral 2) (add first second)) (add (numeral tag) payload) raw
    (weakTrans _ _ _ h1 h2) (pairSum raw (numeral tag) payload hp)
  exact ⟨orderLeft (suc raw) (symm (childSumExpansion first second)) h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
