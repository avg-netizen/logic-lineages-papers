module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- ONE literal tuple: no opaque supplier selection or replacement of components. -/
def structural (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  InstalledExchangeRecursor.structural (OriginalDecodedRank.rank n)
    (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
    (OriginalStructuralDecoderSuppliers.valid n) (OriginalStructuralDecoderSuppliers.window n)
def edge (n : Nat) (arity : Fin n → Nat) : Program 3 := TypedPrimaryEdge.edge (structural n arity)
/-- Only input conversion, not a new opaque recursive supplier: form the code pair
and extract the actual Context window, then run the same standalone exchange. -/
def atContext (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  .composition (OriginalDecodedExchangeEquation.exchange n arity)
    ![InternalApplicationCertificateConstructors.pairOf (.projection 0) (.projection 1),
      InternalApplicationCertificateConstructors.leftOf (.projection 2)]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge
