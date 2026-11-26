module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight sameAccept)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownwardSyntaxProof (typedRename certificateRename)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion OriginalVariableObject
open OriginalVariableObjectSyntaxProof OriginalVariableObjectSupportProof
open OriginalFinalVariableObjectInternalSupportProof (secondTransport)
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalVariableErasureCertificate
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- This is the literal predecessor of the final variable-representative
refinement, including the actual hereditary and application sidecars. -/
def beforeVariable (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    GlobalSourcePackage.Inputs :=
  OriginalNeutralLeaf.refineInputs
    (OriginalConstructorShape.refineInputs
      (OriginalFunctionNeutrality.refineInputs
        (OriginalApplicationSidecar.refineInputs
          (OriginalSpineGuardLeaf.refineInputs
            (OriginalHereditaryLambdaGlobal.prepareInputs
              (OriginalLambdaTraversalSelection.prepareInputs
                (OriginalFinalGuardedRank.refined p H G W)))))))

theorem finalInputs_eq (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalLambdaTraversalSelection.finalInputs (OriginalFinalGuardedRank.refined p H G W) =
      OriginalVariableRepresentative.refineInputs (beforeVariable p H G W) := rfl

/-- The literal packed constructor supplies the original read-only Object
variable test. No variable-test or successor-shape premise is added. -/
theorem shapeVariableObject (tau : Ty) (source gamma extended packed raw : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (TopVariableShape tau source gamma extended packed raw))) :
    Nonempty (Derivation body Delta (variableObject source)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have hv := andLeft (andRight hs)
  have hp := andLeft (andRight (andRight hs))
  have ho := andRight (andRight (andRight hs))
  have htag := OriginalFinalVariableWeakeningSupportProof.packedVariableTag
    packed raw typ (numeral 0) hv hp
  have htest : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (numeral 1) packed)) :=
    sameAccept OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1) z
      (Fin.cons packed Fin.elim0) htag (InternalLessThanSupportProof.zeroConstantValue _)
  exact unaryValue OriginalConstructorLeaf.variableTest InternalUnpair.right
    (numeral 1) packed (Fin.cons source Fin.elim0) htest
    (pairRight source extended packed ho)

/-- The existing variable-certificate proof applies with an internally
accepted window. Its coordinates are supplied by original Program totality;
there is no appeal to native evaluation or calibrated-input reflection. -/
theorem certificateBottomWithWindow (p : GlobalSourcePackage.Inputs) (context : Nat)
    (tau : Ty) (source target witness : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 p.window (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (typed (GlobalSourcePackage.computability (OriginalVariableRepresentative.refineInputs p))
        tau (numeral context) source)))
    (hv : Nonempty (Derivation body Delta (variableObject source)))
    (hc : Nonempty (Derivation body Delta
      (certificate (GlobalSourcePackage.source (OriginalVariableRepresentative.refineInputs p))
        false context source target witness))) :
    Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target)) := by
  apply GlobalSourceSpineQueriesProof.coordinateCases BottomSpineMeasure.measure
    (numeral context) source target _
  intro beta j Theta gammaCode x y parameter _mark _depth hj hg hx hy hp _hm _hd
  rw [bottomAtSourceGammaRename]
  have hw' := unaryRename p.window (numeral 1) (numeral context) hw j Theta hj
  simp only [numeralRename] at hw'
  have ht' := renameInto ht j Theta hj
  simp only [typedRename,numeralRename] at ht'
  have hv' := renameInto hv j Theta hj
  rw [variableObjectRename] at hv'
  have hc' := renameInto hc j Theta hj
  rw [certificateRename] at hc'
  simp only [numeralRename] at hp
  exact OriginalVariableObjectCertificateCoreProof.certificateAtCoordinates
    p context tau (source.relabel j) (target.relabel j) (witness.relabel j)
    gammaCode x y parameter hw' hg hx hy hp ht' hv' hc'

/-- The internally recovered source Gamma agrees with its supplied actual
pair coordinate by selector functionality. The bottom is then at that SAME
Gamma, not an independently chosen context witness. -/
theorem bottomAtKnownGamma (tau : Ty) (source target gamma : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gamma source)))
    (hb : Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target))) :
    Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma)) := by
  apply bottomAtSourceGammaCases tau source target _ hb
  intro beta j Theta actualGamma hj ha hbottom
  rw [bottomGraphRename,numeralRename]
  have hg' := unaryRename InternalUnpair.left gamma source hg j Theta hj
  have he := valueUnique InternalUnpair.left actualGamma (gamma.relabel j)
    (Fin.cons (source.relabel j) Fin.elim0) ha hg'
  apply secondTransport ComputabilityLeast.bottomObject (target.relabel j)
    (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) actualGamma (gamma.relabel j)
  · simpa only [equalEqn] using he
  · exact hbottom

/-- The actual final source certificate determines the target's literal
bottom shape. Every input graph is a factor of the frozen premise. -/
theorem targetBottom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (Premise p H G W context tau source target witness gamma extended packed raw))) :
    Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)) := by
  have hw := andLeft h
  have ht := andLeft (andRight h)
  have hs := andLeft (andRight (andRight h))
  have hc := andRight (andRight (andRight h))
  have hv := shapeVariableObject tau source gamma extended packed raw hs
  have hbottom := certificateBottomWithWindow (beforeVariable p H G W) context tau
    source target witness hw ht hv hc
  exact bottomAtKnownGamma tau source target extended
    (pairLeft source extended packed (andRight (andRight (andRight hs)))) hbottom

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSourceProof
