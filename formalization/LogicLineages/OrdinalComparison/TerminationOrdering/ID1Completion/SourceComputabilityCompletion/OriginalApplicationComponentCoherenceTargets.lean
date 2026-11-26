module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Two original valid applications with the SAME actual final canonical
output have equal actual canonical function and argument outputs. The domain
and codomain may differ initially and are also recovered as equal. Every
constructor witness, source-validity premise and child graph belongs to the
same selected Data, original window and symbolic parameter. No child type,
fixedness, normalization or raw-injectivity premise is supplied. -/
def ActualOriginalApplicationComponentCoherence : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg parent functionOut argumentOut
      arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut'
      out parameter : OrdinaryArithmetic.Term alpha),
  let after := selectedData data window
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceTargets
