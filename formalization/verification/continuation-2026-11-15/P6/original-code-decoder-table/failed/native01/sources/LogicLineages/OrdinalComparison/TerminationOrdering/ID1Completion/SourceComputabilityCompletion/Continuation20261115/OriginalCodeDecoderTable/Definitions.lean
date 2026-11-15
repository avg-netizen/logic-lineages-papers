module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Literal numeric list of count zeros. -/
def zerosStep : Program 2 := .composition InternalListCodec.consCode
  ![constant 2 0,.projection 1]
def zeros : Program 1 := .recursion .zero zerosStep
/-- Original codeTable fuel-zero seed has bound+1 false entries, including index zero. -/
def seed : Program 1 := .composition zeros (fun _ : Fin 1 => succOf (.projection 0))
/-- Base ascending row is singleton codeNext(previous,0), not an empty list. -/
def rowBase (n : Nat) : Program 1 := .composition InternalListCodec.consCode
  ![.composition (OriginalCodeDecoderStep.step n) ![.projection 0,constant 1 0],constant 1 0]
/-- Inputs [index,previous ascending row,old table]. Append, never prepend. -/
def rowStep (n : Nat) : Program 3 := .composition InternalApplicationValidityStackAppend.append
  ![.projection 1,.composition InternalListCodec.consCode
    ![.composition (OriginalCodeDecoderStep.step n) ![.projection 2,succOf (.projection 0)],constant 3 0]]
/-- [bound,previous table] returns exactly cells zero through bound in order. -/
def nextRow (n : Nat) : Program 2 := .recursion (rowBase n) (rowStep n)
/-- Inputs [predecessor fuel,previous table,bound]. -/
def tableStep (n : Nat) : Program 3 := .composition (nextRow n) ![.projection 2,.projection 1]
/-- Inputs [fuel,bound]; exactly the ORIGINAL finite codeTable iteration. -/
def tableProgram (n : Nat) : Program 2 := .recursion seed (tableStep n)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable
