module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorFunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof
open InternalComputabilityApplication InternalComputabilityApplicationProof InternalComputabilityDownward
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalGraphCompositionFunctionalityProof
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalNeutralExpansion OriginalNeutralExpansionTargets OriginalNeutralApplicationSuccessorSupportProof
open UniformCertificateCompletion

/-- Exact original source-certificate successor computability. Only the
first path edge is inverted; its final endpoint remains unrestricted. -/
theorem actualOriginalFinalApplicationSuccessorComputability :
    ActualOriginalFinalApplicationSuccessorComputability := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS alpha Gamma sigma tau F A X Y witness
  let q := OriginalSpineGuardLeaf.refineInputs p
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let B := SourcePresentation.sourceBody (src p) context
  let H := applicationPremises (src p) (comp p) context sigma tau F A X Y witness
  have hh : Nonempty (Derivation B (H :: Gamma) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htyped := andLeft hh
  have hn := andLeft (andRight hh)
  have hs := andLeft (andRight (andRight hh))
  have hg := andLeft (andRight (andRight (andRight hh)))
  have hca := andLeft (andRight (andRight (andRight (andRight hh))))
  have ha := andLeft (andRight (andRight (andRight (andRight (andRight hh)))))
  have hc := andRight (andRight (andRight (andRight (andRight (andRight hh)))))
  have hd := andIntro (andIntro htyped (typedness (comp p) sigma (numeral context) A hca)) hg
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have result : Nonempty (Derivation B (H :: Gamma) (computable (comp p) tau (numeral context) Y)) := by
    apply OriginalSourceNeutralApplicationObjectPathProof.actualOriginalSourceNeutralApplicationObjectPositivePathElimination
      n arity q hq symbols S table hS alpha (H :: Gamma) sigma tau F A X Y witness
      (computable (comp p) tau (numeral context) Y) hd ha hn hc
    · intro beta j Delta hj gammaCode function argument x y parameter raw tail vertex cert hprefix
      simp only [computableRename,numeralRename]
      exact OriginalNeutralApplicationSuccessorBottomProof.bottomCase n arity p hp symbols S table hS
        beta _ sigma tau (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j)
        (witness.relabel j) gammaCode function argument x y parameter raw tail vertex cert
        (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hprefix _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    · intro beta j Delta hj gammaCode function argument x y parameter raw tail vertex cert hprefix
        Sraw T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut haligned G V hobjects
      simp only [computableRename,numeralRename]
      have hca' := renameInto hca j Delta hj
      simp only [computableRename,numeralRename] at hca'
      have hs' := renameInto hs j Delta hj
      rw [OriginalNeutralTypeInductionSyntaxProof.successorsRename] at hs'
      exact OriginalNeutralApplicationSuccessorFunctionProof.functionCase n arity p hp symbols S table hS
        beta Delta sigma tau (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j)
        (witness.relabel j) gammaCode function argument x y parameter raw tail vertex cert
        targetFunctionOut G V child hprefix hobjects
        (andLeft (andRight (andRight (andRight (andRight (andRight (andRight haligned))))))) hca' hs'
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorProof
