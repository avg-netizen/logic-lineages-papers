module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalAcceptanceLeafProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParserSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportLogicalProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exhaustive INTERNAL tag split, including malformed raw inputs. Both
original pair fields are supplied by total programs and are never assumed. -/
theorem rawTagCases (raw : OTerm alpha) (psi : Formula alpha)
    (known : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (i : Fin 8) (payload : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 rawTag (numeral i.val) (raw.relabel j))) →
      Nonempty (Derivation body Theta (StepPair (raw.relabel j) (numeral i.val) payload)) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (other : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (tag payload : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepPair (raw.relabel j) tag payload)) →
      Nonempty (Derivation body Theta (StepUnknownTag tag)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 1 := ![rawTag,rightOf (.projection 0)]
  apply programsCases qs (Fin.cons raw Fin.elim0) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  apply tagCases (ys 0) (psi.relabel j)
  · intro i Xi inc heq
    have htag := outputTransport rawTag (ys 0) (numeral i.val) xs
      (by simpa only [equalEqn] using heq) (weakenProof (hs 0) inc)
    have hleft := unaryValue InternalUnpair.left (.projection 0) (numeral i.val)
      (raw.relabel j) xs htag (projectionValue 0 xs)
    have hpair := pairFields (.projection 0) (raw.relabel j) (numeral i.val) (ys 1) xs
      (projectionValue 0 xs) hleft (weakenProof (hs 1) inc)
    exact known beta j Xi i (ys 1) (fun p hp => inc _ (hj p hp)) htag hpair
  · intro Xi inc hu
    have hleft := unaryValue InternalUnpair.left (.projection 0) (ys 0)
      (raw.relabel j) xs (weakenProof (hs 0) inc) (projectionValue 0 xs)
    have hpair := pairFields (.projection 0) (raw.relabel j) (ys 0) (ys 1) xs
      (projectionValue 0 xs) hleft (weakenProof (hs 1) inc)
    exact other beta j Xi (ys 0) (ys 1) (fun p hp => inc _ (hj p hp)) hpair hu

theorem nilConstructorFromPair (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (he : Nonempty (Derivation body Delta (equal payload z))) :
    Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)) := by
  have hr := outputTransport InternalUnpair.right payload z (Fin.cons raw Fin.elim0)
    (by simpa only [equalEqn] using he) (pairRight raw (numeral 6) payload hp)
  have hpair := reconstructPair raw (numeral 6) z (pairLeft raw (numeral 6) payload hp) hr
  exact binaryValue InternalPairing.pairing (constant 0 6) (constant 0 0) raw (numeral 6) z Fin.elim0
    hpair (constantValue 6 Fin.elim0) (constantValue 0 Fin.elim0)

/-- A tag-six input is the literal nil constructor only AFTER original
acceptance has paid the zero-payload guard. -/
theorem acceptedNilConstructor (H : Program 1) (raw payload types gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H true types raw gamma))) :
    Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)) := by
  have hi := closedApply (actualOriginalTypedInternalNilAcceptance body H alpha raw payload types gamma) hp
  exact nilConstructorFromPair raw payload (hp) (andLeft (iffForward hi ha))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
