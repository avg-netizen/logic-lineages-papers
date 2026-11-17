module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEnumerationRecursion.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.NativeStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalClassCodes
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant addOf)
open Continuation20261114 Continuation20261115
/-- Inputs throughout are [original packed seed, original parameter]. -/
def rootType : Program 2 := leftOf (.projection 0)
def seedRaw : Program 2 := rightOf (.projection 0)
def context : Program 2 := leftOf (.projection 1)
def gamma : Program 2 := rightOf (.projection 1)
def window : Program 2 := leftOf context
def symbols : Program 2 := leftOf window
def types : Program 2 := rightOf window
def bound : Program 2 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => gamma)
def bounds (n : Nat) : Program 2 :=
  .composition (OriginalCodeBoundsRecursion.bounds n) (fun _ : Fin 1 => seedRaw)
def size (n : Nat) : Program 2 := leftOf (bounds n)
def labels (n : Nat) : Program 2 := rightOf (bounds n)
/-- EXACT original term fuel 2*size, not a depth/rank surrogate or list bound. -/
def fuel (n : Nat) : Program 2 := addOf (size n) (size n)
/-- The checked sourceHeads AST emits headNumber; the enumeration input uses
Encodable HeadCode. This explicit map is mandatory, preserving all occurrences. -/
def heads (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition (InternalListMap.map OriginalHeadEncodingBridge.encodeHead)
    (fun _ : Fin 1 => .composition (OriginalSourceHeads.sourceHeads n arity) ![symbols,types])
def node (n : Nat) : Program 2 := pairOf bound (fuel n)
def parameter (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  pairOf types (pairOf (heads n arity) (pairOf (labels n) (size n)))
def enumerated (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition (LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEnumerationRecursion.enumeration n) ![node n,parameter n arity]
/-- Map step [raw code, already mapped tail, unchanged seed root type]. -/
def pairStep : Program 3 := consOf (pairOf (.projection 2) (.projection 0)) (.projection 1)
def pairRoots : Program 2 := InternalRawListRecursion.listRec (constant 1 0) pairStep
def frontend (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition pairRoots ![enumerated n arity,rootType]
/-- Actual typed seed admission, with the concrete original Context decoder.
H is the existing head-signature leaf, NOT a candidate/enumeration oracle. -/
def admitted (n : Nat) (H : Program 1) : Program 2 :=
  OriginalTypedDecoder.target H (OriginalDecodedContextValidity.contextGuard n)
/-- classCodes stage inside the original decoded seed pipeline. Invalid Context
or typed seed yields zero; no candidate filterMap is performed at this stage. -/
def classCodes (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Program 2 :=
  InternalAcceptance.branch (admitted n H) (constant 2 0) (frontend n arity)
/-- Literal original external specification, before the candidate filterMap. -/
def classCodesValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  InternalOriginalUniformParameterLeaves.decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (fun q => TwoSol20261113.CalibratedPrimary.Membership.entriesCode
        (ContextUniformPrimary.classCodes arity ctx.1.1 ctx.1.2 obj.1 q))).getD 0)
    (v.get 0) (v.get 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalClassCodes
