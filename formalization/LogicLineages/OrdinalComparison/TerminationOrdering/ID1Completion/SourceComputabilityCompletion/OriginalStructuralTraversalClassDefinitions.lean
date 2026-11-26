module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClass
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original final source/window/fold premises at the SAME selected tuple. -/
def premises {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha) : Formula alpha :=
  let r := OriginalStructuralTraversalKey.refined p H G W P
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)

/-- Full final traversal retains the original active class of its input.
The class uses the acyclic prior structural key, not the new traversal itself. -/
def AcceptedLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let s := OriginalStructuralClassKeyDefinitions.inputs p H G W
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OTerm alpha),
  Nonempty (Derivation body Delta ((premises p H G W P out input typ parameter).imp
    (OriginalActiveClassKernel.Accepted s H G W
      OriginalRawSyntaxTransport.variableRankPackedRaw P input out parameter)))

/-- Actual initial-minimum outputs on final input and output coincide.
This is NOT equality/idempotence of the final traversal. No class or output
source premise is added; they must be derived from the actual final run. -/
def MinimumLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let s := OriginalStructuralClassKeyDefinitions.inputs p H G W
  let R := (OriginalActiveKernelMinimum.inputs s H G W P).base.oldRepresentative
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter before after : OTerm alpha),
  Nonempty (Derivation body Delta
    ((premises p H G W P out input typ parameter ⊓
      (graph2 R before input parameter ⊓ graph2 R after out parameter)).imp
      (equal before after)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClass
