module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side name for the frozen run followed by the unchanged output. -/
def fold : Program 3 := .composition output (fun _ : Fin 1 => OriginalStructuralNodeSize.run)

def completionBody {α : Type}
    (d k value count produced : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph5 OriginalRawSyntaxTransportInternalMachineState.visitState (.var (.inr 2))
      (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
    graph3 OriginalRawSyntaxTransportInternalMachineState.returnState (.var (.inr 3))
      (produced.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (graph2 (OriginalStructuralNodeSize.iterate) (.var (.inr 3))
      (count.relabel Sum.inl) (.var (.inr 2)))

def Completes {α : Type}
    (d k value count produced : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (completionBody d k value count produced)

abbrev payloadFuel {α : Type} (payload : OTerm α) : OTerm α :=
  InternalApplicationCertifiedResultFoldClosure.payloadFuel payload

def witnessBody {α : Type}
    (d k value payload : OTerm α) : Formula (α ⊕ Fin 2) :=
  InternalPairingSumBounds.weakBound (.var (.inr 0)) (payloadFuel (payload.relabel Sum.inl)) ⊓
    Completes (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl)
      (.var (.inr 0)) (.var (.inr 1))

def HasCompletion {α : Type}
    (d k value payload : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (witnessBody d k value payload)

/-- Strong induction is on the literal raw natural, not a native syntax tree. -/
def rawMatrix {α : Type} (raw : OTerm α) : Formula (α ⊕ Fin 2) :=
  HasCompletion (.var (.inr 0)) (.var (.inr 1)) (raw.relabel Sum.inl) (raw.relabel Sum.inl)

def AtRaw {α : Type} (raw : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (rawMatrix raw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletion
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletion
