module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
public import Mathlib.Data.List.Sort
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSort
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Auxiliary pair: original suffix and the suffix with x inserted.
Input is x. Keeping the original suffix avoids a hidden raw-tail oracle. -/
def insertBase : Program 1 :=
  .composition InternalPairing.pairing ![InternalRawListRecursion.zero,
    .composition InternalListCodec.consCode ![.projection 0,InternalRawListRecursion.zero]]
/-- Inputs [head,previous pair,x]. -/
def originalCons : Program 3 :=
  .composition InternalListCodec.consCode ![.projection 0,
    .composition InternalUnpair.left (fun _ : Fin 1 => .projection 1)]
def beforeCons : Program 3 :=
  .composition InternalListCodec.consCode ![.projection 2,originalCons]
def afterCons : Program 3 :=
  .composition InternalListCodec.consCode ![.projection 0,
    .composition InternalUnpair.right (fun _ : Fin 1 => .projection 1)]
def insertStep : Program 3 :=
  .composition InternalPairing.pairing ![originalCons,
    InternalAcceptance.branch
      (.composition InternalLessThan.ltTest ![.projection 0,.projection 2]) beforeCons afterCons]
/-- Inputs [list,x]. Every raw natural uses the literal zero/cons codec;
there is no failure marker or separate malformed branch. -/
def insertState : Program 2 := InternalRawListRecursion.listRec insertBase insertStep
def insert : Program 2 := .composition InternalUnpair.right (fun _ : Fin 1 => insertState)
/-- Inputs [head,sorted tail], insert reads [list,x]. -/
def sortStep : Program 2 := .composition insert ![.projection 1,.projection 0]
def sort : Program 1 := InternalRawListRecursion.listRec (InternalRawListRecursion.zero : Program 0) sortStep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSort
