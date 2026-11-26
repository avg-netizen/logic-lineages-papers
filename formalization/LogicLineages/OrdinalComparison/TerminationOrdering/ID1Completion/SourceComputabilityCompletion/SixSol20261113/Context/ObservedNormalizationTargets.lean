module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The existing structural preminimum package, without another refinement. -/
def preminimum (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalStructuralClassKeyDefinitions.inputs (Erasure.ObservedPut.prepared p H G W) H G W

def premises {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph (Erasure.ObservedPut.finalInputs p H G W P).window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (Erasure.ObservedPut.finalData p H G W P) input typ parameter ⊓
     InternalParameterizedCanonicalResultFold.foldGraph
      (Erasure.ObservedPut.finalData p H G W P) out input parameter)

/-- Derive the literal all-position relation, including original domains, from
actual complete final folding. No key, rank, scan, or Accepted premise. -/
def ActualAccepted : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((premises p H G W P out input typ parameter).imp
      (OriginalActiveClassKernel.Domain (preminimum p H G W) H G W input parameter ⊓
       (OriginalActiveClassKernel.Domain (preminimum p H G W) H G W out parameter ⊓
        OriginalAllPositionMinimumCoherenceTargets.Accepted
          (preminimum p H G W) H G W P input out parameter))))

/-- Equality of actual outputs of the SAME once-minimum before traversal.
This does not assert equality of complete final folded endpoints or Objects. -/
def ActualMinimum : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter inputMinimum outputMinimum : OTerm alpha),
  let R := (OriginalClassContextAllPositionSelection.inputs (preminimum p H G W) H G W P).base.oldRepresentative
  Nonempty (Derivation body Delta
    (((premises p H G W P out input typ parameter) ⊓
      (graph2 R inputMinimum input parameter ⊓ graph2 R outputMinimum out parameter)).imp
        (equal inputMinimum outputMinimum)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationTargets
