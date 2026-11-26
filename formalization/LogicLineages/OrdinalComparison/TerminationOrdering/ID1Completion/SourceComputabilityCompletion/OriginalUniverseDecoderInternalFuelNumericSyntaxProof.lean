module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionSyntaxProof InternalRawListRecursionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-local direct numeric recursion, definitionally the guarded source's
unchanged Program 3 when instantiated with its binary transition. -/
def repeatStep (transition : Program 2) : Program 4 :=
  .composition transition ![.projection 1,.projection 3]
def repeatProgram (transition : Program 2) : Program 3 :=
  .recursion (.projection (0 : Fin 2)) (repeatStep transition)
def repeatGraph {alpha : Type} (transition : Program 2)
    (out count initial c : OTerm alpha) : Formula alpha :=
  graph3 (repeatProgram transition) out count initial c

@[simp] theorem repeatRename {alpha beta : Type} (transition : Program 2)
    (out count initial c : OTerm alpha) (j : alpha → beta) :
    (repeatGraph transition out count initial c).relabel j =
      repeatGraph transition (out.relabel j) (count.relabel j) (initial.relabel j) (c.relabel j) := by
  simp only [repeatGraph,graph3,programRename,consTermRename,emptyRename]

@[simp] theorem repeatSubst {alpha beta : Type} (transition : Program 2)
    (out count initial c : OTerm alpha) (ts : alpha → OTerm beta) :
    (repeatGraph transition out count initial c).subst (fun a => emb (ts a)) =
      repeatGraph transition (out.subst ts) (count.subst ts) (initial.subst ts) (c.subst ts) := by
  simp only [repeatGraph,graph3,programSubst,consTermSubst,emptySubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSyntaxProof
