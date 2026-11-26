module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Paired component coherence at the actual Data and window of a final
source package. This merely spells out the already frozen internal contract
at a supplied Data; it adds no calibration or normalization premise. -/
def PairedComponents (after : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg parent functionOut argumentOut
      arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut'
      out parameter : OrdinaryArithmetic.Term alpha),
  let source := fun arrow d e fp ap fn arg parent functionOut argumentOut =>
    OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
        (graph2 (InternalOriginalUniformDescentSelection.validity after)
          InternalOriginalStepGuard.one parent parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph after functionOut fn parameter ⊓
            (InternalParameterizedCanonicalResultFold.foldGraph after argumentOut arg parameter ⊓
              InternalParameterizedCanonicalResultFold.foldGraph after out parent parameter))))
  Nonempty (Derivation body Delta
    ((source arrow d e fp ap fn arg parent functionOut argumentOut ⊓
      source arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut').imp
      (InternalControlGraph.equal d d' ⊓ (InternalControlGraph.equal e e' ⊓
        (InternalControlGraph.equal functionOut functionOut' ⊓
          InternalControlGraph.equal argumentOut argumentOut')))))

open Source UniformCertificateCompletion OriginalVariableObject

/-- Choose ONE original tuple before every source window and ambient Gamma.
Its actual sidecar-refined final tuple retains full calibration, the complete
Package, prior root/neutral/variable laws and paired application coherence.
No quotient neutral-inversion or all-term accessibility claim is included. -/
def ActualOriginalApplicationComponentCoherenceGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := OriginalApplicationSidecar.finalInputs p
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     OriginalConstructorShape.FullFoldRootFields (OuterSelection.data r.base r.window) r.window ∧
     OriginalFunctionNeutrality.FullFoldMarkPreservation (OuterSelection.data r.base r.window) r.window ∧
     OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint r) r.window r.oldStep ∧
     PairedComponents (OuterSelection.data r.base r.window) r.window ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalTargets
