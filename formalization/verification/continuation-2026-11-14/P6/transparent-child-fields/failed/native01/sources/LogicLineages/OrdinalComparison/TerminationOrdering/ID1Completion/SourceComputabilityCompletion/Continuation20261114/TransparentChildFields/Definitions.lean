module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
def rawCode (target : Bool) : Program 3 :=
  if target then TransparentTagFields.targetCode else TransparentTagFields.sourceCode
/-- Leaf defaults are original var0 code, which is literally zero. Raw firstOf
is only used on positive arity, since it is not itself defaulted on leaves. -/
def firstRaw (target : Bool) : Program 3 :=
  InternalAcceptance.branch (arityOf (rawCode target)) (constant 3 0) (firstOf (rawCode target))
def secondRaw (target : Bool) : Program 3 :=
  InternalAcceptance.branch (sameOf (arityOf (rawCode target)) (constant 3 2))
    (constant 3 0) (secondOf (rawCode target))
def first (V : Program 3) (target : Bool) : Program 3 :=
  InternalAcceptance.branch V (constant 3 0) (firstRaw target)
def second (V : Program 3) (target : Bool) : Program 3 :=
  InternalAcceptance.branch V (constant 3 0) (secondRaw target)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields
