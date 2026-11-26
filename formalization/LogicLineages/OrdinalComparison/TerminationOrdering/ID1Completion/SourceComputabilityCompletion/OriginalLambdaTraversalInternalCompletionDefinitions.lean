module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def completionBody {α : Type} (leaf : Program 2)
    (value parameter count produced : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph4 OriginalLambdaTraversalInternal.visitState (.var (.inr 2))
      (value.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
    graph3 OriginalLambdaTraversalInternal.returnState (.var (.inr 3))
      (produced.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (graph2 (OriginalLambdaTraversal.iterate leaf) (.var (.inr 3))
      (count.relabel Sum.inl) (.var (.inr 2)))

def Completes {α : Type} (leaf : Program 2)
    (value parameter count produced : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (completionBody leaf value parameter count produced)

abbrev payloadFuel {α : Type} (payload : OTerm α) : OTerm α :=
  InternalApplicationCertifiedResultFoldClosure.payloadFuel payload

def witnessBody {α : Type} (leaf : Program 2)
    (value parameter payload : OTerm α) : Formula (α ⊕ Fin 2) :=
  InternalPairingSumBounds.weakBound (.var (.inr 0)) (payloadFuel (payload.relabel Sum.inl)) ⊓
    Completes leaf (value.relabel Sum.inl) (parameter.relabel Sum.inl)
      (.var (.inr 0)) (.var (.inr 1))

def HasCompletion {α : Type} (leaf : Program 2)
    (value parameter payload : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (witnessBody leaf value parameter payload)

def payloadMatrix {α : Type} (leaf : Program 2) (payload : OTerm α) : Formula (α ⊕ Fin 2) :=
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) (.var (.inr 0))).imp
    (HasCompletion leaf (.var (.inr 0)) (.var (.inr 1)) (payload.relabel Sum.inl))

def AtPayload {α : Type} (leaf : Program 2) (payload : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (payloadMatrix leaf payload)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletion
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletion
