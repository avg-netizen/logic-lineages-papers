module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorFunctionProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalComputabilityApplication InternalComputabilityApplicationProof
open InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalGraphCompositionFunctionalityProof
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalNeutralExpansion OriginalNeutralApplicationSuccessorSupportProof
open UniformCertificateCompletion

/-- The child's ORIGINAL certificate consumes the original all-successors
hypothesis. Application C uses the SAME argument and final tuple, then the
unchanged suffix closes at the unrestricted final Object endpoint. -/
theorem functionCase (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun t => t ∈ S))
    (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter raw tail vertex cert
      targetFunction G V child : OTerm alpha)
    (hprefix : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (OriginalSourceNeutralApplicationPath.RecoveredPrefix (data p) (final p).window (final p).oldStep
        (src p) (comp p) (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau
        F A X Y witness gammaCode function argument x y parameter raw tail vertex cert)))
    (hobjects : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (OriginalSourceApplicationReconstruction.Recovered (data p) (final p).window (comp p)
        (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau F A X
        gammaCode function argument x parameter targetFunction vertex G V)))
    (hchild : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (edgeAccepted (data p) (final p).oldStep function targetFunction child parameter)))
    (hA : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computable (comp p) sigma (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) A)))
    (hF : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computableSuccessors (src p) (comp p) (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (.arrow sigma tau) F))) :
    Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computable (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) Y)) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let B := SourcePresentation.sourceBody (src p) context
  apply OriginalFunctionChildCertificateProof.actualOriginalFinalFunctionChildCertificate p context
    alpha Gamma sigma tau F A X gammaCode function argument x parameter targetFunction vertex G V child
    (computable (comp p) tau (numeral context) Y) hobjects hchild
  intro beta j Delta hj entry pathCode hrec
  simp only [computableRename,numeralRename]
  have hpref := renameInto hprefix j Delta hj
  rw [OriginalSourceNeutralApplicationPathSyntaxProof.recoveredPrefixRename] at hpref
  have hca := renameInto hA j Delta hj
  simp only [computableRename,numeralRename] at hca
  have hsuccessors := renameInto hF j Delta hj
  rw [OriginalNeutralTypeInductionSyntaxProof.successorsRename] at hsuccessors
  have hcert := andRight (andRight (andRight (andRight hrec)))
  have hcg := OriginalNeutralTypeInductionSyntaxProof.successorApply
    (src p) (comp p) context (.arrow sigma tau) (F.relabel j) (G.relabel j)
    hsuccessors (edgeIntroduction hcert)
  have hr := andLeft hrec
  have hdomain := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hr))))))
  have hacc := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hr)))))))
  have hpre := andIntro (andIntro hcg (andIntro (andRight hdomain) hca)) hacc
  obtain ⟨ha⟩ := OriginalApplicationComputabilityProof.actualOriginalFinalAcceptedApplicationComputable
    n arity p hp symbols S table hS B beta Delta sigma tau
    (G.relabel j) (A.relabel j) (V.relabel j)
  obtain ⟨hpre⟩ := hpre
  have hcv : Nonempty (Derivation B Delta
      (computable (comp p) tau (numeral context) (V.relabel j))) :=
    ⟨Derivation.implicationElimination ha hpre⟩
  have hypair := andLeft (andRight (andRight (andRight (andRight (andLeft hpref)))))
  have hvpair := andLeft (andRight (andRight (andRight (andRight hr))))
  have hparameter := OriginalSourceNeutralApplicationFieldsProof.parameterPairOf (andLeft hr)
  have hyt := prefixTargetTyped n arity p hp symbols S table hS sigma tau
    (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
    (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
    (x.relabel j) (y.relabel j) (parameter.relabel j) (raw.relabel j)
    (tail.relabel j) (vertex.relabel j) (cert.relabel j) hpref
  exact suffixComputable n arity p hp symbols S table hS tau
    (V.relabel j) (Y.relabel j) (gammaCode.relabel j) (vertex.relabel j) (y.relabel j)
    (parameter.relabel j) (tail.relabel j) hvpair hypair hparameter hyt hcv
    (andRight (andRight (andRight (andRight hpref))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorFunctionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorFunctionProof
