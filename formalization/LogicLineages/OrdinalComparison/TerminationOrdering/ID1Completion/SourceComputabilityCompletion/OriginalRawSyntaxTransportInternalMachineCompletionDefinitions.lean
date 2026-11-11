module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def completionBody {α : Type} (mode : Mode)
    (d k value count produced : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph5 OriginalRawSyntaxTransportInternalMachineState.visitState (.var (.inr 2))
      (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
    graph3 OriginalRawSyntaxTransportInternalMachineState.returnState (.var (.inr 3))
      (produced.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (graph2 (OriginalRawSyntaxTransport.iterate mode) (.var (.inr 3))
      (count.relabel Sum.inl) (.var (.inr 2)))

def Completes {α : Type} (mode : Mode)
    (d k value count produced : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (completionBody mode d k value count produced)

abbrev payloadFuel {α : Type} (payload : OTerm α) : OTerm α :=
  InternalApplicationCertifiedResultFoldClosure.payloadFuel payload

def witnessBody {α : Type} (mode : Mode)
    (d k value payload : OTerm α) : Formula (α ⊕ Fin 2) :=
  InternalPairingSumBounds.weakBound (.var (.inr 0)) (payloadFuel (payload.relabel Sum.inl)) ⊓
    Completes mode (d.relabel Sum.inl) (k.relabel Sum.inl) (value.relabel Sum.inl)
      (.var (.inr 0)) (.var (.inr 1))

def HasCompletion {α : Type} (mode : Mode)
    (d k value payload : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (witnessBody mode d k value payload)

/-- Strong induction is on the literal raw natural, not a native syntax tree. -/
def rawMatrix {α : Type} (mode : Mode) (raw : OTerm α) : Formula (α ⊕ Fin 2) :=
  HasCompletion mode (.var (.inr 0)) (.var (.inr 1)) (raw.relabel Sum.inl) (raw.relabel Sum.inl)

def AtRaw {α : Type} (mode : Mode) (raw : OTerm α) : Formula α :=
  InternalClosedPrograms.allBlock (rawMatrix mode raw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletion
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletion
