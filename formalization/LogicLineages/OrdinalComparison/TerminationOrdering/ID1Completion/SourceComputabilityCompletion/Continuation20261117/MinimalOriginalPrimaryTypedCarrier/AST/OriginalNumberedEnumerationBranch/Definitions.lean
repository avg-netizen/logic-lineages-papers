module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalTypeListsEnumeration.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalNumberedEnumerationBranch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal right-nested six-field products in original label/head/type/base/
types/extras order. Every occurrence is preserved. -/
def product56 : Program 6 := .composition NumericDependencyCross.cross ![.projection 4,.projection 5]
def product456 : Program 6 := .composition NumericDependencyCross.cross ![.projection 3,product56]
def product3456 : Program 6 := .composition NumericDependencyCross.cross ![.projection 2,product456]
def product23456 : Program 6 := .composition NumericDependencyCross.cross ![.projection 1,product3456]
def product123456 : Program 6 := .composition NumericDependencyCross.cross ![.projection 0,product23456]
/-- Factor only the outer tag of the literal original numberedConstructor.
Its payload is already the unchanged right-nested six-field product. -/
def tagPayload : Program 1 := InternalApplicationCertificateConstructors.pairOf
  (OriginalRawSyntaxTransport.constant 1 5) (.projection 0)
def branch : Program 6 := .composition (InternalListMap.map tagPayload)
  (fun _ : Fin 1 => product123456)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalNumberedEnumerationBranch
