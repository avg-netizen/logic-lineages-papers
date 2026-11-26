module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalObservedClassProof (sameKnownLeft sameKnownRight)
open OriginalActiveClassKernel
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev keyGraph (R : Program 2) (seed candidate parameter : OTerm alpha) : Formula alpha :=
  graph3 (keyTest R) (suc z) seed candidate parameter

abbrev observerGraph (O : Program 1) (seed candidate parameter : OTerm alpha) : Formula alpha :=
  graph3 (observerTest O) (suc z) seed candidate parameter

@[simp] theorem keyGraphRename {beta : Type} (R : Program 2)
    (seed candidate parameter : OTerm alpha) (j : alpha → beta) :
    (keyGraph R seed candidate parameter).relabel j =
      keyGraph R (seed.relabel j) (candidate.relabel j) (parameter.relabel j) := by
  simp only [keyGraph,graph3Rename,sucRelabel,zRelabel]

@[simp] theorem observerGraphRename {beta : Type} (O : Program 1)
    (seed candidate parameter : OTerm alpha) (j : alpha → beta) :
    (observerGraph O seed candidate parameter).relabel j =
      observerGraph O (seed.relabel j) (candidate.relabel j) (parameter.relabel j) := by
  simp only [observerGraph,graph3Rename,sucRelabel,zRelabel]

/-- Build the actual binary-key equality from two equal computed outputs. -/
theorem keyAccept (R : Program 2) (seed candidate parameter value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 R value seed parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 R value candidate parameter))) :
    Nonempty (Derivation body Delta (keyGraph R seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  exact sameAccept (.composition R ![.projection 0,.projection 2])
    (.composition R ![.projection 1,.projection 2]) value xs
    (binaryValue R (.projection 0) (.projection 2) value seed parameter xs
      hs (projectionValue 0 xs) (projectionValue 2 xs))
    (binaryValue R (.projection 1) (.projection 2) value candidate parameter xs
      hc (projectionValue 1 xs) (projectionValue 2 xs))

/-- A key hit transports an actual original-key value to the candidate. -/
theorem keyTransfer (R : Program 2) (seed candidate parameter value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (keyGraph R seed candidate parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 R value seed parameter))) :
    Nonempty (Derivation body Delta (graph2 R value candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  have hs' := binaryValue R (.projection 0) (.projection 2) value seed parameter xs
    hs (projectionValue 0 xs) (projectionValue 2 xs)
  have hc := sameKnownLeft (.composition R ![.projection 0,.projection 2])
    (.composition R ![.projection 1,.projection 2]) value xs hk hs'
  exact binaryRecover R (.projection 1) (.projection 2) value candidate parameter xs
    hc (projectionValue 1 xs) (projectionValue 2 xs)

theorem keyOfEqual (R : Program 2) (seed candidate parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (keyGraph R seed candidate parameter)) := by
  apply programCases R (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [keyGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have he' := renameInto he j Theta hj
  simp only [InternalTagArithmeticSyntaxProof.eqnRelabel] at he'
  obtain ⟨he'⟩ := he'
  exact keyAccept R (seed.relabel j) (candidate.relabel j) (parameter.relabel j) value hv
    (headTransport R value (seed.relabel j) (candidate.relabel j)
      (Fin.cons (parameter.relabel j) Fin.elim0) ⟨symm he'⟩ hv)

/-- The shared old-key output proves equality of whole acceptance rows. -/
theorem keyRowForward (R : Program 2) (seed other probe parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (keyGraph R seed other parameter)))
    (hp : Nonempty (Derivation body Delta (keyGraph R seed probe parameter))) :
    Nonempty (Derivation body Delta (keyGraph R other probe parameter)) := by
  apply programCases R (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [keyGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have ho' := renameInto ho j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [keyGraphRename] at ho' hp'
  exact keyAccept R (other.relabel j) (probe.relabel j) (parameter.relabel j) value
    (keyTransfer R (seed.relabel j) (other.relabel j) (parameter.relabel j) value ho' hv)
    (keyTransfer R (seed.relabel j) (probe.relabel j) (parameter.relabel j) value hp' hv)

theorem keyRowBackward (R : Program 2) (seed other probe parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (keyGraph R seed other parameter)))
    (hp : Nonempty (Derivation body Delta (keyGraph R other probe parameter))) :
    Nonempty (Derivation body Delta (keyGraph R seed probe parameter)) := by
  apply programCases R (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [keyGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have ho' := renameInto ho j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [keyGraphRename] at ho' hp'
  exact keyAccept R (seed.relabel j) (probe.relabel j) (parameter.relabel j) value hv
    (keyTransfer R (other.relabel j) (probe.relabel j) (parameter.relabel j) value hp'
      (keyTransfer R (seed.relabel j) (other.relabel j) (parameter.relabel j) value ho' hv))

theorem observerAccept (O : Program 1) (seed candidate parameter value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 O value seed)))
    (hc : Nonempty (Derivation body Delta (graph1 O value candidate))) :
    Nonempty (Derivation body Delta (observerGraph O seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  exact sameAccept (.composition O (fun _ : Fin 1 => .projection 1))
    (.composition O (fun _ : Fin 1 => .projection 0)) value xs
    (unaryValue O (.projection 1) value candidate xs hc (projectionValue 1 xs))
    (unaryValue O (.projection 0) value seed xs hs (projectionValue 0 xs))

theorem observerTransfer (O : Program 1) (seed candidate parameter value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (observerGraph O seed candidate parameter)))
    (hs : Nonempty (Derivation body Delta (graph1 O value seed))) :
    Nonempty (Derivation body Delta (graph1 O value candidate)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  have hs' := unaryValue O (.projection 0) value seed xs hs (projectionValue 0 xs)
  have hc := sameKnownRight (.composition O (fun _ : Fin 1 => .projection 1))
    (.composition O (fun _ : Fin 1 => .projection 0)) value xs hk hs'
  exact unaryRecover O (.projection 1) value candidate xs hc (projectionValue 1 xs)

theorem observerOfEqual (O : Program 1) (seed candidate parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (observerGraph O seed candidate parameter)) := by
  apply programCases O (Fin.cons seed Fin.elim0) _
  intro beta j Theta value hj hv
  rw [observerGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have he' := renameInto he j Theta hj
  simp only [InternalTagArithmeticSyntaxProof.eqnRelabel] at he'
  obtain ⟨he'⟩ := he'
  exact observerAccept O (seed.relabel j) (candidate.relabel j) (parameter.relabel j) value hv
    (headTransport O value (seed.relabel j) (candidate.relabel j) Fin.elim0 ⟨symm he'⟩ hv)

theorem observerRowForward (O : Program 1) (seed other probe parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observerGraph O seed other parameter)))
    (hp : Nonempty (Derivation body Delta (observerGraph O seed probe parameter))) :
    Nonempty (Derivation body Delta (observerGraph O other probe parameter)) := by
  apply programCases O (Fin.cons seed Fin.elim0) _
  intro beta j Theta value hj hv
  rw [observerGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have ho' := renameInto ho j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [observerGraphRename] at ho' hp'
  exact observerAccept O (other.relabel j) (probe.relabel j) (parameter.relabel j) value
    (observerTransfer O (seed.relabel j) (other.relabel j) (parameter.relabel j) value ho' hv)
    (observerTransfer O (seed.relabel j) (probe.relabel j) (parameter.relabel j) value hp' hv)

theorem observerRowBackward (O : Program 1) (seed other probe parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observerGraph O seed other parameter)))
    (hp : Nonempty (Derivation body Delta (observerGraph O other probe parameter))) :
    Nonempty (Derivation body Delta (observerGraph O seed probe parameter)) := by
  apply programCases O (Fin.cons seed Fin.elim0) _
  intro beta j Theta value hj hv
  rw [observerGraphRename]
  simp only [consTermRename,emptyRename] at hv
  have ho' := renameInto ho j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [observerGraphRename] at ho' hp'
  exact observerAccept O (seed.relabel j) (probe.relabel j) (parameter.relabel j) value hv
    (observerTransfer O (other.relabel j) (probe.relabel j) (parameter.relabel j) value hp'
      (observerTransfer O (seed.relabel j) (other.relabel j) (parameter.relabel j) value ho' hv))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEqualityProof
