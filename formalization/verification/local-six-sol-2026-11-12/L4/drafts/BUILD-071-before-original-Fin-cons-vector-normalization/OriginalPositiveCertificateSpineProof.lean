module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (projectionValue)
open OriginalSpineGuardLeafInternalProof (conjunctionPreserves leafHasSpineGuard)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem wrapperSpine (endpoint : Program 6) (window : Program 1) (leaf : Program 4) :
    OriginalSpineGuardLeaf.LeafHasSpineGuard
      (OriginalHereditaryLambdaGlobal.wrapper endpoint window leaf) := by
  unfold OriginalHereditaryLambdaGlobal.wrapper OriginalConstructorLeaf.refined OriginalNeutralLeaf.refined
  exact conjunctionPreserves _ _ (conjunctionPreserves _ _ (leafHasSpineGuard leaf))

theorem finalLeafSpine (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    OriginalSpineGuardLeaf.LeafHasSpineGuard (preparedKernelFinalInputs p H G W P).oldStep := by
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let seed := OriginalTransparentMinimum.minimumInputs H G Q q
  change OriginalSpineGuardLeaf.LeafHasSpineGuard
    (OriginalLambdaTraversalSelection.finalInputs (OriginalFinalGuardedRank.refined seed H G W)).oldStep
  rw [ClosedSelectionProof.actualFinalClosedLeafIdentity]
  exact wrapperSpine _ _ _

theorem parameterWindow (window : Program 1) (context : Nat) (x parameter gamma : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gamma))) :
    Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window x parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![x,parameter]
  have hwindow : Nonempty (Derivation body Delta
      (graph1 window InternalOriginalStepGuard.one (numeral context))) := by
    simpa only [numeral,InternalOriginalStepGuard.one] using hw
  exact unaryValue window (leftOf (.projection 1)) InternalOriginalStepGuard.one
    (numeral context) xs hwindow
    (unaryValue InternalUnpair.left (.projection 1) (numeral context) parameter xs
      (pairLeft parameter (numeral context) gamma hp) (projectionValue 1 xs))

/-- The actual final leaf's outer spine factor and the original full-fold
mark theorem pay both suppliers of quotientGuard at this literal tuple. -/
theorem quotientSpine (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat)
    (x y quotient parameter gamma : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gamma)))
    (he : Nonempty (Derivation body Delta
      (edgeAccepted (preparedKernelFinalData p H G W P)
        (preparedKernelFinalInputs p H G W P).oldStep x y quotient parameter))) :
    Nonempty (Derivation body Delta
      (OriginalSpineGuardLeaf.spineAccepted x y quotient parameter)) := by
  let f := preparedKernelFinalInputs p H G W P
  let D := preparedKernelFinalData p H G W P
  exact OriginalQuotientSpineProof.quotientGuard D f.window f.oldStep
    (OriginalFullFoldSpineProof.actualOriginalFullFoldSpinePreservation f.base f.window)
    (OriginalSelectedStepSpineProof.rawStepHasSpineGuard D f.oldStep
      (finalLeafSpine p H G W P))
    x y quotient parameter (parameterWindow f.window context x parameter gamma hw hp) he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateSpineProof
