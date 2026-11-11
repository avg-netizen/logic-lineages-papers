module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomPathProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion

/-- Expose the literal preceding variable-preserving selector only once,
in a small module; the original ordinary suffix code remains unchanged. -/
theorem finalBottomPathIdentity (p : GlobalSourcePackage.Inputs)
    {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (x y code parameter : OTerm alpha) :
    let r := OriginalApplicationSidecar.finalInputs (OriginalSpineGuardLeaf.refineInputs p)
    Nonempty (Derivation body Gamma (OriginalVariableRepresentative.windowGraph r.window x parameter)) →
    Nonempty (Derivation body Gamma (OriginalVariableQuotientPath.bottomAccepted x)) →
    Nonempty (Derivation body Gamma
      (InternalParameterizedPathChecker.pathGraph
        (edgeChecker (OuterSelection.data r.base r.window) r.oldStep) x y code parameter)) →
    Nonempty (Derivation body Gamma (equal y x)) := by
  let q := OriginalSpineGuardLeaf.refineInputs p
  let previous := OriginalNeutralLeaf.refineInputs
    (OriginalConstructorShape.refineInputs (OriginalFunctionNeutrality.refineInputs
      (OriginalApplicationSidecar.refineInputs q)))
  exact OriginalVariableQuotientPathPathCoreProof.bottomPathIdentity
    previous.base previous.window previous.oldStep x y code parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomPathProof
