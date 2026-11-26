module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Root structural-key preservation by the SAME already-defined all-position
observed final tuple. This is neither the older active-kernel tuple nor a new
hereditary-evaluator key. No root-key, Accepted, fixedness, or canonical-output
hypothesis is supplied. No equality of final folded endpoints is asserted. -/
def ActualRootKeyPreservation : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph
        (Erasure.ObservedPut.finalInputs p H G W P).window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
        (Erasure.ObservedPut.finalData p H G W P) input typ parameter ⊓
       InternalParameterizedCanonicalResultFold.foldGraph
        (Erasure.ObservedPut.finalData p H G W P) out input parameter)).imp
      ((InternalApplicationCertificateConstructors.graph2 (Erasure.ObservedPut.key p H G W) mark out parameter).iff
       (InternalApplicationCertificateConstructors.graph2 (Erasure.ObservedPut.key p H G W) mark input parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyTargets
