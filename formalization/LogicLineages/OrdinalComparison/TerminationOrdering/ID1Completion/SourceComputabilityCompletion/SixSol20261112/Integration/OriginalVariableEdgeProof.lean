module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalComputabilityDownwardProof (edgeCases)
open InternalComputabilityDownwardSyntaxProof (typedRename)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalErasureCertificateContinuationSyntaxProof (shapeRename)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalVariableEdgeTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The checked explicit new certificate existential is precisely the
original source edge, with its original binder and original checker. -/
theorem resultIdentity (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat)
    (source target erasedSource erasedTarget : OTerm alpha) :
    Result p H G W P context source target erasedSource erasedTarget =
      CorrectedOriginalVariableDichotomyTargets.Result p H G W P context
        source target erasedSource erasedTarget := by
  unfold Result CorrectedOriginalVariableDichotomyTargets.Result
  rw [InternalAccessibilityRulesSyntaxProof.edgeExists]
  rfl

/-- Eliminate the OLD original edge's existential certificate internally,
apply the all-index source theorem, and retain its actual erased endpoints. -/
theorem atEdge (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (tau : Ty)
    (source target gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (Premise p H G W P context tau source target gamma extended packed raw domain index)))
    (hes : Nonempty (Derivation body Delta
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target))) :
    Nonempty (Derivation body Delta
      (Result p H G W P context source target erasedSource erasedTarget)) := by
  rw [resultIdentity]
  let f := preparedKernelFinalInputs p H G W P
  apply edgeCases (GlobalSourcePackage.source f) context source target _
    (andRight (andRight (andRight h)))
  intro beta j Theta certificate hj hc
  rw [OriginalVariableDichotomyProof.resultRename]
  have hw := renameInto (andLeft h) j Theta hj
  rw [graph1Rename] at hw
  simp only [numeralRename] at hw
  have ht := renameInto (andLeft (andRight h)) j Theta hj
  rw [typedRename] at ht
  simp only [numeralRename] at ht
  have hs := renameInto (andLeft (andRight (andRight h))) j Theta hj
  rw [shapeRename] at hs
  have hes' := renameInto hes j Theta hj
  have het' := renameInto het j Theta hj
  rw [graph1Rename] at hes' het'
  have hp : Nonempty (Derivation body Theta
      (OriginalErasureCertificateContinuation.Premise
        (Erasure.VariableSourceErasureTargets.preparedSeed p H G W P) H G W context tau
        (source.relabel j) (target.relabel j) certificate (gamma.relabel j)
        (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
        (index.relabel j))) :=
    andIntro hw (andIntro ht (andIntro hs hc))
  exact OriginalVariableDichotomyProof.atIndex p H G W P context tau
    (source.relabel j) (target.relabel j) certificate (gamma.relabel j)
    (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
    (index.relabel j) (erasedSource.relabel j) (erasedTarget.relabel j) hp hes' het'

theorem actualOriginalVariableEdgeErasure : ActualOriginalVariableEdgeErasure := by
  intro p H G W P body alpha Delta context tau source target gamma extended
    packed raw domain index erasedSource erasedTarget
  let A := Premise p H G W P context tau source target gamma extended packed raw domain index ⊓
    (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
      graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := atEdge p H G W P context tau source target gamma extended packed raw
    domain index erasedSource erasedTarget (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableEdgeProof
