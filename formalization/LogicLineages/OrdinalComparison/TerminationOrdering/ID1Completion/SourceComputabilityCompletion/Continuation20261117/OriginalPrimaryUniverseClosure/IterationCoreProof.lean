module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalBetaTotalityProof InternalQuotientComparisonProof
open Iteration IterationSyntaxProof SyntaxProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowApply (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter out context gamma : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount n arity count pool reached parameter gamma context)))
    (hi : Nonempty (Derivation body Delta
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity)) out count pool reached parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached gamma context))) :
    Nonempty (Derivation body Delta (allAccepted n arity out gamma context)) := by
  obtain ⟨h⟩ := elimination body alpha 1 Delta (matrix n arity count pool reached parameter gamma context)
    (fun _ => emb out) hrow
  rw [matrixWitness] at h
  obtain ⟨hi⟩ := hi
  obtain ⟨hu⟩ := hu
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hi) hu⟩

theorem zeroCore (n : Nat) (arity : Fin n → Nat)
    (pool reached parameter out context gamma : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity)) out z pool reached parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached gamma context))) :
    Nonempty (Derivation body Delta (allAccepted n arity out gamma context)) := by
  have he := valueUnique (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
    out reached ![z,pool,reached,parameter] hi
    (PrimaryIteration.RecursionProof.zeroValue (OriginalConcreteStructuralEdge.edge n arity) pool reached parameter)
  apply InvariantProof.introduce n arity out gamma context
  intro beta j Theta candidate typ raw hj hm hp
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  have hu' := renameInto hu j Theta hj
  rw [allAcceptedRename] at hu'
  have hm' := headTransport contains (numeral 1) (out.relabel j) (reached.relabel j)
    (Fin.cons candidate Fin.elim0) he' hm
  exact InvariantProof.eliminate n arity (reached.relabel j) candidate typ raw
    (gamma.relabel j) (context.relabel j) hu' hm' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
