module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSelectorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def requestSelectors {n : Nat} (p : Program n) : Fin 4 → Program n :=
  ![leftOf p,leftOf (rightOf p),leftOf (rightOf (rightOf p)),rightOf (rightOf (rightOf p))]

 theorem requestFields {n : Nat} (p : Program n)
    (code mode gamma typ raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hm : Nonempty (Derivation body Delta (programGraph (leftOf p) mode xs)))
    (hg : Nonempty (Derivation body Delta (programGraph (leftOf (rightOf p)) gamma xs)))
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf p))) typ xs)))
    (hr : Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf p))) raw xs))) :
    Nonempty (Derivation body Delta (StepRequest code mode gamma typ raw)) := by
  apply queryCases (![rightOf p,rightOf (rightOf p)] : Fin 2 → Program n) xs _
  intro beta j ys Theta hj hq
  rw [stepRequestRename]
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [programRename] at hp' hm' hg' ht' hr'
  let xx := fun i => (xs i).relabel j
  have h0 := pairFields p (code.relabel j) (mode.relabel j) (ys 0) xx hp' hm' (hq 0)
  have h1 := pairFields (rightOf p) (ys 0) (gamma.relabel j) (ys 1) xx (hq 0) hg' (hq 1)
  have h2 := pairFields (rightOf (rightOf p)) (ys 1) (typ.relabel j) (raw.relabel j) xx (hq 1) ht' hr'
  exact stepRequestIntro _ _ _ _ _ ys (andIntro h0 (andIntro h1 h2))

 theorem requestFieldValue {n : Nat} (p : Program n) (i : Fin 4)
    (code mode gamma typ raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepRequest code mode gamma typ raw))) :
    Nonempty (Derivation body Delta
      (programGraph (requestSelectors p i) (![mode,gamma,typ,raw] i) xs)) := by
  apply stepRequestCases code mode gamma typ raw _ hf
  intro beta j Theta ys hj hq
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun k => (xs k).relabel j
  have htail0 := pairRightValue p (code.relabel j) (mode.relabel j) (ys 0) xx hp' (andLeft hq)
  have htail1 := pairRightValue (rightOf p) (ys 0) (gamma.relabel j) (ys 1) xx htail0 (andLeft (andRight hq))
  have h0 := pairLeftValue p (code.relabel j) (mode.relabel j) (ys 0) xx hp' (andLeft hq)
  have h1 := pairLeftValue (rightOf p) (ys 0) (gamma.relabel j) (ys 1) xx htail0 (andLeft (andRight hq))
  have h2 := pairLeftValue (rightOf (rightOf p)) (ys 1) (typ.relabel j) (raw.relabel j) xx htail1 (andRight (andRight hq))
  have h3 := pairRightValue (rightOf (rightOf p)) (ys 1) (typ.relabel j) (raw.relabel j) xx htail1 (andRight (andRight hq))
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => ?_))) i
  · exact h0
  · exact h1
  · exact h2
  · obtain rfl : k = 0 := Fin.eq_zero k
    exact h3

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSelectorsProof
