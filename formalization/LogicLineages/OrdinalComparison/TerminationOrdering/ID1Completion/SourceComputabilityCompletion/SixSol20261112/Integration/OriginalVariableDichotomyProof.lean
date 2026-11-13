module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedOriginalVariableDichotomyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof (headTransport zeroSuccessorCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open InternalComputabilityDownwardSyntaxProof (typedRename certificateRename)
open OriginalErasureCertificateContinuationSyntaxProof (shapeRename)
open OriginalVariableErasureCertificateSyntaxProof (internalEqualRename originalRankDropRename)
open Erasure.VariableSourceErasureSyntaxProof (witnessRename)
open UniformCertificateCompletion CorrectedOriginalVariableDichotomyTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Equality changes only the literal variable-constructor input. The actual
old source certificate, type, context and all selected Programs remain fixed. -/
theorem indexTransport (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn index other)))
    (h : Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.Premise p H G W context tau
        source target witness gamma extended packed raw domain index))) :
    Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.Premise p H G W context tau
        source target witness gamma extended packed raw domain other)) := by
  have shape := andLeft (andRight (andRight h))
  have hv := andLeft (andRight shape)
  have hv' : Nonempty (Derivation body Delta
      (graph1 OriginalRawSyntaxTransport.variableConstructor raw other)) :=
    headTransport OriginalRawSyntaxTransport.variableConstructor raw index other Fin.elim0 he hv
  have shape' := andIntro (andLeft shape)
    (andIntro hv' (andRight (andRight shape)))
  exact andIntro (andLeft h)
    (andIntro (andLeft (andRight h))
      (andIntro shape' (andRight (andRight (andRight h)))))

theorem premiseRename {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index : OTerm alpha) (j : alpha → beta) :
    (OriginalErasureCertificateContinuation.Premise p H G W context tau
      source target witness gamma extended packed raw domain index).relabel j =
    OriginalErasureCertificateContinuation.Premise p H G W context tau
      (source.relabel j) (target.relabel j) (witness.relabel j) (gamma.relabel j)
      (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j) (index.relabel j) := by
  simp only [OriginalErasureCertificateContinuation.Premise,conjunctionRename,
    graph1Rename,numeralRename,typedRename,certificateRename,shapeRename]

theorem originalOrRename {beta : Type} (phi psi : Formula alpha) (j : alpha → beta) :
    (phi ⊔ psi).relabel j = phi.relabel j ⊔ psi.relabel j := rfl

theorem resultRename {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat)
    (source target erasedSource erasedTarget : OTerm alpha) (j : alpha → beta) :
    (Result p H G W P context source target erasedSource erasedTarget).relabel j =
      Result p H G W P context (source.relabel j) (target.relabel j)
        (erasedSource.relabel j) (erasedTarget.relabel j) := by
  simp only [Result,originalOrRename,conjunctionRename,internalEqualRename,
    originalRankDropRename,witnessRename]

/-- The actual original arithmetic zero/successor split binds its predecessor
internally. Both alternatives use source proofs at the same final tuple. -/
theorem atIndex (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.Premise
        (Erasure.VariableSourceErasureTargets.preparedSeed p H G W P) H G W context tau
        source target witness gamma extended packed raw domain index)))
    (hes : Nonempty (Derivation body Delta
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target))) :
    Nonempty (Derivation body Delta
      (Result p H G W P context source target erasedSource erasedTarget)) := by
  let seed := Erasure.VariableSourceErasureTargets.preparedSeed p H G W P
  apply zeroSuccessorCases Delta index _
  · let Theta := eqn index z :: Delta
    have inc : ∀ phi ∈ Delta, phi ∈ Theta := fun _ hp => List.mem_cons_of_mem _ hp
    have h' : Nonempty (Derivation body Theta
        (OriginalErasureCertificateContinuation.Premise seed H G W context tau
          source target witness gamma extended packed raw domain index)) := by
      obtain ⟨h⟩ := h
      exact ⟨Derivation.weakening inc h⟩
    have hes' : Nonempty (Derivation body Theta
        (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source)) := by
      obtain ⟨hes⟩ := hes
      exact ⟨Derivation.weakening inc hes⟩
    have het' : Nonempty (Derivation body Theta
        (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)) := by
      obtain ⟨het⟩ := het
      exact ⟨Derivation.weakening inc het⟩
    have hz : Nonempty (Derivation body Theta (eqn index (numeral 0))) := by
      have hzero : numeral 0 = (z : OTerm alpha) := by rw [numeral]
      rw [hzero]
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := indexTransport seed H G W context tau source target witness gamma
      extended packed raw domain index (numeral 0) hz h'
    obtain ⟨hc⟩ := Erasure.TopDomainProof.originalArbitraryDomainTopCollapse
      seed H G W body alpha Theta context tau source target witness gamma extended
      packed raw domain erasedSource erasedTarget
    obtain ⟨ha⟩ := andIntro hp (andIntro hes' het')
    have hr : Nonempty (Derivation body Theta
        (equal domain (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) ⊓
          OriginalVariableErasureCertificate.RawResult tau source target gamma extended
            erasedSource erasedTarget)) := ⟨Derivation.implicationElimination hc ha⟩
    obtain ⟨collapsed⟩ := andRight (andRight (andRight (andRight hr)))
    exact ⟨orLeft collapsed⟩
  · intro beta j Theta predecessor hj he
    rw [resultRename]
    have h' := renameInto h j Theta hj
    rw [premiseRename] at h'
    have hes' := renameInto hes j Theta hj
    have het' := renameInto het j Theta hj
    rw [graph1Rename] at hes' het'
    have hp := indexTransport seed H G W context tau
      (source.relabel j) (target.relabel j) (witness.relabel j) (gamma.relabel j)
      (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
      (index.relabel j) (suc predecessor) he h'
    obtain ⟨hc⟩ := Erasure.VariableSourceErasureProof.actualOriginalSurvivingVariableSourceErasure
      p H G W P body beta Theta context tau
      (source.relabel j) (target.relabel j) (witness.relabel j) (gamma.relabel j)
      (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
      predecessor (erasedSource.relabel j) (erasedTarget.relabel j)
    obtain ⟨ha⟩ := andIntro hp (andIntro hes' het')
    exact ⟨orRight (Derivation.conjunctionRight (Derivation.implicationElimination hc ha))⟩

theorem actualOriginalVariableSourceErasureDichotomy : ActualOriginalVariableSourceErasureDichotomy := by
  intro p H G W P body alpha Delta context tau source target witness gamma extended
    packed raw domain index erasedSource erasedTarget
  let A := OriginalErasureCertificateContinuation.Premise
      (Erasure.VariableSourceErasureTargets.preparedSeed p H G W P) H G W context tau
      source target witness gamma extended packed raw domain index ⊓
    (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
      graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := atIndex p H G W P context tau source target witness gamma extended
    packed raw domain index erasedSource erasedTarget (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyProof
