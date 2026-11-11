module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawObjectTransport OriginalRawObjectTransportInternalSyntaxProof
open OriginalContextInsertionSupportProof (binaryInputs)
open InternalParameterizedCanonicalResultFold (foldN foldGraph)
open InternalOriginalUniformDescentSelection (selectedTyped)
open OriginalTransparentDecoderValidatorCollapse UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem windowRename (window : Program 1) (context : Nat)
    (h : Nonempty (Derivation body Delta (graph1 window (numeral 1) (numeral context))))
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Nonempty (Derivation body Theta (graph1 window (numeral 1) (numeral context))) := by
  simpa only [graph1Rename,numeralRename] using renameInto h j Theta hj

 theorem outerTypedRename (typed : Program 3) (context : Nat) (typ input : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph3 typed (numeral 1) (numeral context) typ input)))
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Nonempty (Derivation body Theta
      (graph3 typed (numeral 1) (numeral context) (typ.relabel j) (input.relabel j))) := by
  simpa only [graph3Rename,numeralRename] using renameInto h j Theta hj

/-- Construct the original Context/Gamma parameter by actual Program totality. -/
 theorem parameterCases (context : Nat) (gamma : OTerm alpha) (psi : Formula alpha)
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ h ∈ Delta, h.relabel j ∈ Theta) → ∀ parameter : OTerm beta,
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing parameter (numeral context) (gamma.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases InternalPairing.pairing
    (Fin.cons (numeral context) (Fin.cons gamma Fin.elim0)) psi
  intro beta j Theta parameter hj hp
  apply k beta j Theta hj parameter
  simpa only [consTermRename,emptyRename,numeralRename] using hp

/-- Expose the ACTUAL unchanged canonical Object Program at known genuine
input coordinates. Functionality identifies those coordinates with its own
internally bound ones; no output identity or fixedness is assumed. -/
 theorem canonicalCasesAtPair (p : GlobalSourcePackage.Inputs)
    (context input out gamma raw : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma raw)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram p) out context input)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ h ∈ Delta, h.relabel j ∈ Theta) → ∀ parameter canonicalRaw : OTerm beta,
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing parameter (context.relabel j) (gamma.relabel j))) →
      Nonempty (Derivation body Theta
        (foldGraph (OriginalLambdaTraversalSelection.finalData p)
          canonicalRaw (raw.relabel j) parameter)) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (out.relabel j) (gamma.relabel j) canonicalRaw)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply (OriginalFinalVariableObjectExposureProof.actualOriginalFinalVariableObjectExposure p).1
    body alpha Delta context input out psi hk
  intro beta j Theta hj actualGamma actualRaw parameter canonicalRaw h
  have hp' := binaryRename InternalPairing.pairing input gamma raw hp j Theta hj
  have hex := andLeft h
  have hg := valueUnique InternalUnpair.left actualGamma (gamma.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0)
    (pairLeft _ _ _ hex) (pairLeft _ _ _ hp')
  have hr := valueUnique InternalUnpair.right actualRaw (raw.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0)
    (pairRight _ _ _ hex) (pairRight _ _ _ hp')
  have hparameter := binaryInputs InternalPairing.pairing parameter (context.relabel j)
    actualGamma (context.relabel j) (gamma.relabel j) ⟨refl _⟩ hg (andLeft (andRight h))
  have hfold := headTransport (foldN (OriginalLambdaTraversalSelection.finalData p))
    canonicalRaw actualRaw (raw.relabel j) (Fin.cons parameter Fin.elim0) hr
    (andLeft (andRight (andRight h)))
  have hout := binaryInputs InternalPairing.pairing (out.relabel j) actualGamma canonicalRaw
    (gamma.relabel j) canonicalRaw hg ⟨refl _⟩ (andRight (andRight (andRight h)))
  exact k beta j Theta hj parameter canonicalRaw hparameter hfold hout

/-- Recover the literal selected typed checker from the original active
outer dispatch. The only additional facts are actual pair/parameter graphs. -/
 theorem outerRecover (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ input gamma raw parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ input)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gamma))) :
    Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) raw typ parameter)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  exact OuterCarrierSupportProof.typedRecover f.oldComp (selected p H G W) f.window
    f.oldVertex f.oldResult context typ input gamma raw parameter
    hw (pairLeft _ _ _ hp) (pairRight _ _ _ hp) hq ht

/-- Rebuild the SAME original outer typed dispatch from the canonical raw
output, including its original type-tag and Object validity wrappers. -/
 theorem outerAccept (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ out gamma raw parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out gamma raw)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gamma)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) raw typ parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ out)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  exact OuterTypedProof.typedAccept f.oldComp (selected p H G W) f.window f.oldVertex f.oldResult
    context typ out gamma raw parameter hw (pairLeft _ _ _ hp) (pairRight _ _ _ hp) hq ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
