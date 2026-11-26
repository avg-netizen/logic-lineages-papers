module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open GuardedErasureFinalGraphsProof VariableSourceErasureTargets VariableSourceErasureSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Only the original quotient, entry and singleton constructors. -/
def codeQueries : Fin 3 → Program 3 :=
  let entry := pairOf (.projection 1) edgeCode
  ![edgeCode,entry,consOf entry (InternalAcceptance.constantZero 3)]

theorem fromStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (parameter gamma s typ raw t step first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (numeral context) gamma)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (hw : Nonempty (Derivation body Delta (stepAccepted (finalData p H G W P) (finalLeaf p H G W P) s t step parameter)))
    (hfs : Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) s s parameter)))
    (hft : Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) t t parameter)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first gamma s)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing second gamma t))) :
    Nonempty (Derivation body Delta (CertificateWitness p H G W P context first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons step Fin.elim0))
  apply queryCases codeQueries xs _
  intro beta j ys Theta hj hq
  rw [witnessRename]
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm beta := Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons (step.relabel j) Fin.elim0))
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have hs' := renameInto hs j Theta hj
  have hw' := renameInto hw j Theta hj
  have hfs' := renameInto hfs j Theta hj
  have hft' := renameInto hft j Theta hj
  have ho' := renameInto ho j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ha'
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp' hs' ho' ht'
  simp only [stepAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hfs' hft'
  have hedge : Nonempty (Derivation body Theta
      (graph3 edgeCode (ys 0) (s.relabel j) (t.relabel j) (step.relabel j))) := hq 0
  have hentry := binaryRecover InternalPairing.pairing (.projection 1) edgeCode
    (ys 1) (t.relabel j) (ys 0) xx (hq 1) (projectionValue 1 xx) (hq 0)
  have hpath := binaryRecover InternalListCodec.consCode (pairOf (.projection 1) edgeCode)
    (InternalAcceptance.constantZero 3) (ys 2) (ys 1) z xx (hq 2) (hq 1) (constantZeroValue xx)
  have fields : Nonempty (Derivation body Theta
      (Integration.StepObjectCertificateFields p H G W P context
        (parameter.relabel j) (gamma.relabel j) (s.relabel j) (typ.relabel j) (raw.relabel j)
        (t.relabel j) (step.relabel j) (s.relabel j) (t.relabel j)
        (ys 0) (ys 1) (ys 2) (first.relabel j) (second.relabel j))) :=
    andIntro (andIntro ha' hp') (andIntro (andIntro hs' hw')
      (andIntro (andIntro hfs' hft') (andIntro (andIntro hedge (andIntro hentry hpath)) (andIntro ho' ht'))))
  obtain ⟨law⟩ := Integration.OriginalPositiveCertificateProof.actualPreparedKernelStepObjectCertificate
    p H G W P body beta Theta context
    (parameter.relabel j) (gamma.relabel j) (s.relabel j) (typ.relabel j) (raw.relabel j)
    (t.relabel j) (step.relabel j) (s.relabel j) (t.relabel j)
    (ys 0) (ys 1) (ys 2) (first.relabel j) (second.relabel j)
  obtain ⟨fields⟩ := fields
  exact witnessIntro p H G W P context (first.relabel j) (second.relabel j) (ys 2)
    ⟨Derivation.implicationElimination law fields⟩

/-- A scratch deterministic nil step on the literal new variable suffices
for the ORIGINAL positive certificate at the actual erased Object pairs. -/
theorem fromVariable (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (parameter gamma s typ raw index t first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (numeral context) gamma)))
    (hpack : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hfs : Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) s s parameter)))
    (hft : Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) t t parameter)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first gamma s)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing second gamma t))) :
    Nonempty (Derivation body Delta (CertificateWitness p H G W P context first second)) := by
  apply programCases OriginalTransparentDirectBottom.certificateCode (Fin.cons s Fin.elim0) _
  intro beta j Theta cert hj hc
  rw [witnessRename]
  simp only [consTermRename,emptyRename] at hc
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have hpack' := renameInto hpack j Theta hj
  have hv' := renameInto hv j Theta hj
  have hs' := renameInto hs j Theta hj
  have hb' := renameInto hb j Theta hj
  have hfs' := renameInto hfs j Theta hj
  have hft' := renameInto hft j Theta hj
  have ho' := renameInto ho j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ha' hv' hb'
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp' hpack' hs' ho' ht'
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hfs' hft'
  have hw := VariableSourceErasureStepProof.atCertificate p H G W P
    (s.relabel j) (raw.relabel j) (index.relabel j) (typ.relabel j) (t.relabel j) cert
    (parameter.relabel j) hv' hpack' hs' hb' hc
  exact fromStep p H G W P context (parameter.relabel j) (gamma.relabel j)
    (s.relabel j) (typ.relabel j) (raw.relabel j) (t.relabel j) cert (first.relabel j) (second.relabel j)
    ha' hp' hpack' hw hfs' hft' ho' ht'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureCertificateProof
