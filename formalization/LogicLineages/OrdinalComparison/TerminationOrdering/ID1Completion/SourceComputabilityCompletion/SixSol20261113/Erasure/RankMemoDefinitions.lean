module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf)
open ObservationDescentDefinitions
/-- Inputs [typed child observation, current stage i, newest-first table]. The
ORIGINAL subtract AST takes [subtrahend,minuend], hence this is i-childE. -/
def lookupWeight : Program 3 := .composition InternalRawListRecursion.lookup
 ![.composition InternalEqualityTest.subtract ![rightOf (.projection 0),.projection 1],.projection 2]
/-- Step inputs [i,table]. This stage computes code i+1, not i. -/
def nextCode : Program 2 := succOf (.projection 0)
def recursiveRoot : Program 2 := leftOf (rightOf nextCode)
def tag : Program 2 := leftOf recursiveRoot
def payload : Program 2 := rightOf recursiveRoot
def typedAt (slot : DirectSlot) : Program 2 :=
 .composition (select (directPath slot)) (fun _ : Fin 1 => payload)
def directRank (slot : DirectSlot) : Program 2 :=
 .composition lookupWeight ![typedAt slot,.projection 0,.projection 1]
def rowAt (slot : ListSlot) : Program 2 :=
 .composition (select (listPath slot)) (fun _ : Fin 1 => payload)
def rowRank (slot : ListSlot) : Program 2 :=
 .composition (SortWeightedDefinitions.weighted lookupWeight) ![rowAt slot,.projection 0,.projection 1]
def sum (a b : Program 2) : Program 2 := .composition InternalArithmeticPrograms.addition ![a,b]
/-- A NEW proof-side numeric decoder, NOT a replacement for the original
hereditary evaluator or any selected canonical tuple. Variable counts are1,
bottom counts0, and BASE is summed in its actual stored sorted order. -/
def nextValue : Program 2 :=
 OriginalTypedDecoder.ifSame tag (constant 2 0) (constant 2 1)
 (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody)
 (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument))
 (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0)
 (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase)
 (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras))
 (constant 2 0))))))
/-- Choice of total fallback at code0. This does NOT claim that a source-admitted
FULL evaluator output can be0. A recursive-root observation can be0, which is
not the same code. Source calibration/zero exclusion remains a separate proof. -/
def tableBase : Program 0 := consOf (constant 0 1) (constant 0 0)
def tableStep : Program 2 := consOf nextValue (.projection 1)
def table : Program 1 := .recursion tableBase tableStep
def decoder : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => table)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDefinitions
