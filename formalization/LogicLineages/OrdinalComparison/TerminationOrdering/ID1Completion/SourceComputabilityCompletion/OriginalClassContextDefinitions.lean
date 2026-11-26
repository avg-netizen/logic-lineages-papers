module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion OriginalActiveClassKernel OriginalActiveKernelMinimum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Converse of active minimum coherence, at one actual runtime parameter.
The common value is the output of BOTH genuine representative graphs, not
an assumed class-key equality or semantic/native interpretation. -/
def SharedOutputLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let R := (inputs p H G W P).base.oldRepresentative
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed other out parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Domain p H G W seed parameter ⊓
      (Domain p H G W other parameter ⊓
        (graph2 R out seed parameter ⊓ graph2 R out other parameter))).imp
      (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
        seed other parameter)))

/-- Exact internal characterization of equality of actual active representative
outputs. This reduces same-context cancellation to the original class relation;
it does NOT supply cross-context transport of the pre-minimum key. -/
def OutputEquivalenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let R := (inputs p H G W P).base.oldRepresentative
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed other out otherOut parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Domain p H G W seed parameter ⊓
      (Domain p H G W other parameter ⊓
        (graph2 R out seed parameter ⊓ graph2 R otherOut other parameter))).imp
      ((equal out otherOut).iff
        (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
          seed other parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextDefinitions
