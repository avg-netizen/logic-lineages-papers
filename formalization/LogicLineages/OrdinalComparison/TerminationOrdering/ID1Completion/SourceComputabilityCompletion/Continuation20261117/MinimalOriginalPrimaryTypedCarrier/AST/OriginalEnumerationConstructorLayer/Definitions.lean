module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalAscendingRange.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedNumberedEnumerationBranch.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEnumerationConstructorLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Input order throughout: [types,encoded heads,labels,tuple bound,variable
bound,prior,opened]. The original head codec is NOT the raw head-number codec. -/
def tagPayload (tag : Nat) : Program 1 := InternalApplicationCertificateConstructors.pairOf
  (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)
def variableBranch : Program 7 := .composition (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor)
  (fun _ : Fin 1 => .composition LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalAscendingRange.range ![.projection 4])
def lambdaPairs : Program 7 := .composition NumericDependencyCross.cross ![.projection 0,.projection 6]
def lambdas : Program 7 := .composition (InternalListMap.map (tagPayload 1)) (fun _ : Fin 1 => lambdaPairs)
def childPairs : Program 7 := .composition NumericDependencyCross.cross ![.projection 5,.projection 5]
def typedChildPairs : Program 7 := .composition NumericDependencyCross.cross ![.projection 0,childPairs]
def applications : Program 7 := .composition (InternalListMap.map (tagPayload 2)) (fun _ : Fin 1 => typedChildPairs)
def bottoms : Program 7 := .composition (InternalListMap.map OriginalRawSyntaxTransport.bottomConstructor) ![.projection 0]
def convertedHeads (n : Nat) : Program 7 :=
  .composition (LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![.projection 1]
def ordinaryPairs (n : Nat) : Program 7 := .composition NumericDependencyCross.cross ![convertedHeads n,.projection 5]
def ordinary (n : Nat) : Program 7 := .composition (InternalListMap.map (tagPayload 4)) (fun _ : Fin 1 => ordinaryPairs n)
def labelRange : Program 7 := .composition LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalAscendingRange.range
  ![.composition .succ ![.projection 2]]
def typeTuples : Program 7 := .composition LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalTypeListsEnumeration.enumeration ![.projection 3,.projection 0]
def numbered (n : Nat) : Program 7 := .composition (LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedNumberedEnumerationBranch.branch n)
  ![labelRange,.projection 1,.projection 0,.projection 5,typeTuples,.projection 5]
def nils : Program 7 := .composition InternalListCodec.consCode
  ![.composition OriginalRawSyntaxTransport.nilConstructor Fin.elim0,InternalAcceptance.constantZero 7]
def argumentCons : Program 7 := .composition (InternalListMap.map (tagPayload 7)) (fun _ : Fin 1 => typedChildPairs)
/-- The original eight blocks, with every repeated occurrence and row-major
product order retained. Each numeric slot is the corresponding original block. -/
def components (n : Nat) : Fin 8 → Program 7 :=
  ![variableBranch,lambdas,applications,bottoms,ordinary n,numbered n,nils,argumentCons]
def join (a b : Program 7) : Program 7 := .composition InternalApplicationValidityStackAppend.append ![a,b]
/-- Literal left-associated source append order, not sorting or deduplication. -/
def layer (n : Nat) : Program 7 :=
  join (join (join (join (join (join (join variableBranch lambdas) applications) bottoms)
    (ordinary n)) (numbered n)) nils) argumentCons
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEnumerationConstructorLayer
