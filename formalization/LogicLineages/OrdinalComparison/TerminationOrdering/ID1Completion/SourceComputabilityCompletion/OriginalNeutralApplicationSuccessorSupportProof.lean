module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalPropertiesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineComputableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalComputabilityApplication InternalComputabilityApplicationProof InternalComputabilityDownward
open InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalGraphCompositionFunctionalityProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open OriginalSourceNeutralApplicationFieldsProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev final (p : GlobalSourcePackage.Inputs) :=
  OriginalApplicationSidecar.finalInputs (OriginalSpineGuardLeaf.refineInputs p)
abbrev data (p : GlobalSourcePackage.Inputs) := OuterSelection.data (final p).base (final p).window
abbrev src (p : GlobalSourcePackage.Inputs) := GlobalSourcePackage.source (final p)
abbrev comp (p : GlobalSourcePackage.Inputs) := GlobalSourcePackage.computability (final p)

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Typing of the original own output, then original source-certificate
closure. Runtime Gamma and every original coordinate stay symbolic. -/
theorem prefixTargetTyped (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun t => t ∈ S))
    (sigma tau : Ty) (F A X Y witness gammaCode function argument x y parameter raw tail vertex cert : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (OriginalSourceNeutralApplicationPath.RecoveredPrefix (data p) (final p).window (final p).oldStep
        (src p) (comp p) (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau
        F A X Y witness gammaCode function argument x y parameter raw tail vertex cert))) :
    Nonempty (Derivation body Gamma
      (typed (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) Y)) := by
  let r := final p
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity
    (OriginalSpineGuardLeaf.refineInputs p) (OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp)
  have hw := GlobalSourceSpineLeastProof.windowEvaluation n r.window hr.2.1 symbols S table hS
  have hwg := GuardedSourceCertificateProof.windowNumeral (body := body) (Gamma := Gamma)
    (α := alpha) r.window context hw
  have hi := andLeft (andLeft h)
  have hx := outputPairOf hi
  have hraw := InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped
    (data p) (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
    (numeral (typeNumber tau)) function argument x parameter (applicationPremisesOf hi)
  have hxt := OuterTypedProof.typedAccept r.oldComp (data p) r.window r.oldVertex r.oldResult
    context (numeral (typeNumber tau)) X gammaCode x parameter hwg
    (pairLeft X gammaCode x hx) (pairRight X gammaCode x hx) (parameterPairOf hi) hraw
  have hc := andLeft (andRight (andRight (andRight (andLeft h))))
  exact OuterDomainCertificateProof.targetTyped r.oldSrc r.oldComp (data p)
    (RawScalar.checker (data p)) r.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    r.window r.oldVertex r.oldResult context tau X Y witness hw hxt hc

/-- At an exact original suffix, equality transports C in the nil branch;
the unchanged positive source certificate invokes the retained Package. -/
theorem suffixComputable (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun t => t ∈ S))
    (tau : Ty) (V Y gammaCode vertex y parameter tail : OTerm alpha)
    (hVpair : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (graph2 InternalPairing.pairing V gammaCode vertex)))
    (hYpair : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (graph2 InternalPairing.pairing Y gammaCode y)))
    (hparameter : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (graph2 InternalPairing.pairing parameter
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gammaCode)))
    (hYtyped : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (typed (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) Y)))
    (hV : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computable (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) V)))
    (htail : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (InternalParameterizedPathChecker.pathGraph (edgeChecker (data p) (final p).oldStep)
        vertex y tail parameter))) :
    Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computable (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) Y)) := by
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := final p
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let B := SourcePresentation.sourceBody (src p) context
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  have hw := GlobalSourceSpineLeastProof.windowEvaluation n r.window hr.2.1 symbols S table hS
  have hwg := GuardedSourceCertificateProof.windowNumeral (body := B) (Gamma := Gamma)
    (α := alpha) r.window context hw
  have hvt := typedness (comp p) tau (numeral context) V hV
  have hvr := OuterCarrierSupportProof.typedRecover r.oldComp (data p) r.window r.oldVertex r.oldResult
    context (numeral (typeNumber tau)) V gammaCode vertex parameter hwg
    (pairLeft V gammaCode vertex hVpair) (pairRight V gammaCode vertex hVpair) hparameter hvt
  have hyr := OuterCarrierSupportProof.typedRecover r.oldComp (data p) r.window r.oldVertex r.oldResult
    context (numeral (typeNumber tau)) Y gammaCode y parameter hwg
    (pairLeft Y gammaCode y hYpair) (pairRight Y gammaCode y hYpair) hparameter hYtyped
  obtain ⟨hs⟩ := OriginalSameCodeSuffixProof.actualOriginalSameCodeFinalObjectSuffix p context
    B alpha Gamma V Y gammaCode vertex y tail (numeral (typeNumber tau)) parameter
  obtain ⟨ha⟩ := andIntro hwg (andIntro hparameter (andIntro hVpair
    (andIntro hYpair (andIntro hvr (andIntro hyr htail)))))
  have hc := Derivation.implicationElimination hs ha
  let L := equal tail z ⊓ equal V Y
  let R := (equal tail z).not ⊓ certificate (src p) false context V Y tail
  have left : Nonempty (Derivation B (L :: Gamma) (computable (comp p) tau (numeral context) Y)) := by
    have he : Nonempty (Derivation B (L :: Gamma) (eqn V Y)) := by
      rw [← equalEqn]
      exact andRight (show Nonempty (Derivation B (L :: Gamma) L) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact computableTransport (comp p) tau (numeral context) V Y he
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hV L)
  have right : Nonempty (Derivation B (R :: Gamma) (computable (comp p) tau (numeral context) Y)) := by
    have he := edgeIntroduction (andRight
      (show Nonempty (Derivation B (R :: Gamma) R) from ⟨Derivation.hypothesis List.mem_cons_self⟩))
    have package := (OriginalObjectApplicationSpineGlobalPropertiesProof.properties n arity q hq).2.1
    have down := (package.2.2.2 symbols S table hS).2.2.2.2.2 tau alpha V Y
    exact closedApply down (andIntro
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hV R) he)
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hc
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorSupportProof
