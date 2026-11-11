module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Original numbered metadata order: label, head, result, base, types, extras. -/
def numberedSelectors {n : Nat} (p : Program n) : Fin 6 → Program n :=
  ![leftOf p,leftOf (rightOf p),leftOf (rightOf (rightOf p)),
    leftOf (rightOf (rightOf (rightOf p))),
    leftOf (rightOf (rightOf (rightOf (rightOf p)))),
    rightOf (rightOf (rightOf (rightOf (rightOf p))))]

 theorem numberedFields {n : Nat} (p : Program n)
    (code label head result base types extras : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hv : ∀ i : Fin 6, Nonempty (Derivation body Delta
      (programGraph (numberedSelectors p i) (![label,head,result,base,types,extras] i) xs))) :
    Nonempty (Derivation body Delta (StepNumberedPayload code label head result base types extras)) := by
  let qs : Fin 4 → Program n := ![rightOf p,rightOf (rightOf p),
    rightOf (rightOf (rightOf p)),rightOf (rightOf (rightOf (rightOf p)))]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [stepNumberedPayloadRename]
  have hp' := renameInto hp j Theta hj
  have hv' := fun i => renameInto (hv i) j Theta hj
  simp only [programRename] at hp' hv'
  let xx := fun i => (xs i).relabel j
  have h0 := pairFields p (code.relabel j) (label.relabel j) (ys 0) xx hp' (hv' 0) (hq 0)
  have h1 := pairFields (rightOf p) (ys 0) (head.relabel j) (ys 1) xx (hq 0) (hv' 1) (hq 1)
  have h2 := pairFields (rightOf (rightOf p)) (ys 1) (result.relabel j) (ys 2) xx (hq 1) (hv' 2) (hq 2)
  have h3 := pairFields (rightOf (rightOf (rightOf p))) (ys 2) (base.relabel j) (ys 3) xx
    (hq 2) (hv' 3) (hq 3)
  have h4 := pairFields (rightOf (rightOf (rightOf (rightOf p)))) (ys 3)
    (types.relabel j) (extras.relabel j) xx (hq 3) (hv' 4) (hv' 5)
  exact stepNumberedPayloadIntro _ _ _ _ _ _ _ ys
    (andIntro h0 (andIntro h1 (andIntro h2 (andIntro h3 h4))))

 theorem numberedFieldValue {n : Nat} (p : Program n) (i : Fin 6)
    (code label head result base types extras : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepNumberedPayload code label head result base types extras))) :
    Nonempty (Derivation body Delta
      (programGraph (numberedSelectors p i) (![label,head,result,base,types,extras] i) xs)) := by
  apply stepNumberedPayloadCases code label head result base types extras _ hf
  intro beta j Theta ys hj hq
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun k => (xs k).relabel j
  have ht0 := pairRightValue p (code.relabel j) (label.relabel j) (ys 0) xx hp' (andLeft hq)
  have ht1 := pairRightValue (rightOf p) (ys 0) (head.relabel j) (ys 1) xx ht0 (andLeft (andRight hq))
  have ht2 := pairRightValue (rightOf (rightOf p)) (ys 1) (result.relabel j) (ys 2) xx ht1
    (andLeft (andRight (andRight hq)))
  have ht3 := pairRightValue (rightOf (rightOf (rightOf p))) (ys 2) (base.relabel j) (ys 3) xx ht2
    (andLeft (andRight (andRight (andRight hq))))
  have h0 := pairLeftValue p (code.relabel j) (label.relabel j) (ys 0) xx hp' (andLeft hq)
  have h1 := pairLeftValue (rightOf p) (ys 0) (head.relabel j) (ys 1) xx ht0 (andLeft (andRight hq))
  have h2 := pairLeftValue (rightOf (rightOf p)) (ys 1) (result.relabel j) (ys 2) xx ht1
    (andLeft (andRight (andRight hq)))
  have h3 := pairLeftValue (rightOf (rightOf (rightOf p))) (ys 2) (base.relabel j) (ys 3) xx ht2
    (andLeft (andRight (andRight (andRight hq))))
  have h4 := pairLeftValue (rightOf (rightOf (rightOf (rightOf p)))) (ys 3)
    (types.relabel j) (extras.relabel j) xx ht3 (andRight (andRight (andRight (andRight hq))))
  have h5 := pairRightValue (rightOf (rightOf (rightOf (rightOf p)))) (ys 3)
    (types.relabel j) (extras.relabel j) xx ht3 (andRight (andRight (andRight (andRight hq))))
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => ?_))))) i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · obtain rfl : k = 0 := Fin.eq_zero k
    exact h5

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
