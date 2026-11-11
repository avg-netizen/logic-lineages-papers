module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionTypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalComputabilityDownward
open InternalComputabilityDownwardSyntaxProof (typedRename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion

/-- Original output typing is recovered at the accepted Object; no external
membership premise or computability of its function is needed. -/
theorem outputTyped (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) :
    let q := OriginalSpineGuardLeaf.refineInputs p
    let r := OriginalApplicationSidecar.finalInputs q
    let comp := GlobalSourcePackage.computability r
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
      (sigma tau : Ty) (F A X : OTerm alpha),
    Nonempty (Derivation body Gamma (domain comp context sigma tau F A)) →
    Nonempty (Derivation body Gamma (accepted comp sigma tau (numeral context) F A X)) →
    Nonempty (Derivation body Gamma (typed comp tau (numeral context) X)) := by
  dsimp only
  intro body alpha Gamma sigma tau F A X hd ha
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let data := OuterSelection.data r.base r.window
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  have hw := GlobalSourceSpineLeastProof.windowEvaluation n r.window hr.2.1 symbols S table hS
  have inputs := OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
    n arity q hq symbols S table hS
  apply inputs body alpha Gamma sigma tau F A X _ hd ha
  intro beta j Delta hj gammaCode function argument out parameter h
  simp only [typedRename,numeralRename]
  have htyped := InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped data
    (numeral (NumberedLeastCodeRepresentative.typeNumber (.arrow sigma tau)))
    (numeral (NumberedLeastCodeRepresentative.typeNumber sigma))
    (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) function argument out parameter
    (OriginalSourceNeutralApplicationFieldsProof.applicationPremisesOf h)
  have hpair := OriginalSourceNeutralApplicationFieldsProof.outputPairOf h
  have hwindow := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Delta) (α := beta) r.window context hw
  exact OuterTypedProof.typedAccept r.oldComp data r.window r.oldVertex r.oldResult context
    (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) (X.relabel j) gammaCode out parameter
    hwindow (pairLeft _ _ _ hpair) (pairRight _ _ _ hpair)
    (OriginalSourceNeutralApplicationFieldsProof.parameterPairOf h) htyped

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionTypingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionTypingProof
