module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open Continuation20261114
/-- Literal list of ground-type zeros; primitive-recursion inputs are [index,previous]. -/
def groundListStep : Program 2 := consOf (constant 2 0) (.projection 1)
def groundList : Program 1 := .recursion (constant 0 0) groundListStep
/-- Fixed finite arity table, with ordinary lookup behavior outside the bound. -/
def arityAt (n : Nat) (arity : Fin n → Nat) : Program 1 :=
  .composition InternalRawListRecursion.lookup
    ![.projection 0,constant 1 (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))]
/-- Head-payload argument lists, in the ORIGINAL order, not sorted/multiset encoding. -/
def branchArguments (n : Nat) (arity : Fin n → Nat) : Nat → Program 1
  | 4 => consOf (succOf (.projection 0)) (consOf InternalUnpair.left (constant 1 0))
  | 5 => .composition groundList (fun _ : Fin 1 => arityAt n arity)
  | _ => constant 1 0
def atPayload (n : Nat) (arity : Fin n → Nat) (tag : Nat) : Program 1 :=
  .composition (branchArguments n arity tag) (fun _ : Fin 1 => InternalUnpair.right)
def arguments (n : Nat) (arity : Fin n → Nat) : Program 1 :=
  OriginalHeadEncodingBridge.choose 4 (atPayload n arity 4)
    (OriginalHeadEncodingBridge.choose 5 (atPayload n arity 5) (constant 1 0))
/-- A literal head signature AST chosen before every runtime input. Unsupported
raw heads, including invalid basic payloads and out-of-bound ranked symbols,
return zero; valid heads return successor(pair(result,ordered arguments)). -/
def signature (n : Nat) (arity : Fin n → Nat) : Program 1 :=
  InternalAcceptance.branch (Continuation20261115.OriginalHeadDecoderValidity.check n)
    (constant 1 0) (succOf (pairOf OriginalHeadResult.headResult (arguments n arity)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature
