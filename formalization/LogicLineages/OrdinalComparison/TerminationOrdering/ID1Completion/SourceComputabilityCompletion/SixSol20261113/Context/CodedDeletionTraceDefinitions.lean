module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (existsOne)
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal nested-pair record [left,right,parameter,gamma,count,cutoff,type].
The trace itself uses the original raw-list codec, never a semantic list. -/
def record : Program 7 := pairOf (.projection 0)
 (pairOf (.projection 1) (pairOf (.projection 2) (pairOf (.projection 3)
  (pairOf (.projection 4) (pairOf (.projection 5) (.projection 6))))))
def leftField : Program 1 := leftOf (.projection 0)
def rightField : Program 1 := leftOf (rightOf (.projection 0))
def parameterField : Program 1 := leftOf (rightOf (rightOf (.projection 0)))
def gammaField : Program 1 := leftOf (rightOf (rightOf (rightOf (.projection 0))))
def countField : Program 1 := leftOf (rightOf (rightOf (rightOf (rightOf (.projection 0)))))
def cutoffField : Program 1 := leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0))))))
def typeField : Program 1 := rightOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0))))))

/-- Four actual record projections, without source/evaluation assertions. -/
def StateFields {alpha : Type} (entry left right parameter gamma : OTerm alpha) : Formula alpha :=
 graph1 leftField left entry ⊓ (graph1 rightField right entry ⊓
 (graph1 parameterField parameter entry ⊓ graph1 gammaField gamma entry))
def Metadata {alpha : Type} (entry count cutoff selectedType : OTerm alpha) : Formula alpha :=
 graph1 countField count entry ⊓ (graph1 cutoffField cutoff entry ⊓
 graph1 typeField selectedType entry)
def stateMatrix {alpha : Type} (trace index left right parameter gamma : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 graph2 InternalRawListRecursion.lookup (.var (.inr 0)) (index.relabel Sum.inl) (trace.relabel Sum.inl) ⊓
 StateFields (.var (.inr 0)) (left.relabel Sum.inl) (right.relabel Sum.inl)
   (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
def StateAt {alpha : Type} (trace index left right parameter gamma : OTerm alpha) : Formula alpha :=
 existsOne (stateMatrix trace index left right parameter gamma)

/-- Existential actual adjacent records, their literal projections, and EXACT
original operational Transition. No intermediate admission or equality. -/
def stepMatrix {alpha : Type} (trace index c : OTerm alpha) : Formula (alpha ⊕ Fin 13) :=
 let v : Fin 13 → OTerm (alpha ⊕ Fin 13) := fun i => .var (.inr i)
 graph2 InternalRawListRecursion.lookup (v 0) (index.relabel Sum.inl) (trace.relabel Sum.inl) ⊓
 (graph2 InternalRawListRecursion.lookup (v 1) (suc (index.relabel Sum.inl)) (trace.relabel Sum.inl) ⊓
 (StateFields (v 0) (v 2) (v 3) (v 4) (v 5) ⊓
 (Metadata (v 0) (v 6) (v 7) (v 8) ⊓
 (StateFields (v 1) (v 9) (v 10) (v 11) (v 12) ⊓
 DeletionChainDefinitions.Transition (v 2) (v 3) (v 9) (v 10) (v 4) (v 11)
   (c.relabel Sum.inl) (v 5) (v 12) (v 6) (v 7) (v 8)))))
def StepAt {alpha : Type} (trace index c : OTerm alpha) : Formula alpha :=
 block (stepMatrix trace index c)
def stepsBody {alpha : Type} (trace steps c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 (OriginalContextInsertion.Below (.var (.inr 0)) (steps.relabel Sum.inl)).imp
 (StepAt (trace.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl))
/-- One INTERNAL bounded universal, not an external family of step derivations. -/
def AllSteps {alpha : Type} (trace steps c : OTerm alpha) : Formula alpha :=
 allBlock (stepsBody trace steps c)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceDefinitions
