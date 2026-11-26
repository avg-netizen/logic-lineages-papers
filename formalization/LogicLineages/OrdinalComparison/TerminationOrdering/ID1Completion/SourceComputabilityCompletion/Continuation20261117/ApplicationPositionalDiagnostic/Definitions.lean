module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Empty symbol type; no ranked-symbol or arity assumption. -/
def arity : Fin 0 → Nat := fun i => Fin.elim0 i
def ground : Ty := .ground
def arrow : Ty := .arrow ground ground
def head : HeadCode (Fin 0) := .application ground ground
def window : List Ty := [ground, arrow]
def base : Code (Fin 0) :=
  .argumentsCons arrow (.bottom arrow) (.argumentsCons ground (.bottom ground) .argumentsNil)
def target : Code (Fin 0) :=
  .argumentsCons ground (.bottom ground) (.argumentsCons arrow (.bottom arrow) .argumentsNil)
def left : Code (Fin 0) := .ordinary head base
def right : Code (Fin 0) := .ordinary head target
/-- Deliberately permissive fixed M/W, not claimed to be an installed finite-window tuple. -/
def allow : Program 2 := OriginalRawSyntaxTransport.constant 2 1
/-- Literal original termCheck with calibrated concrete H and fixed constant-one M/W.
This is not OriginalUniverseDecoder.source, and asserts nothing about an outer G. -/
def checker : Program 4 := OriginalUniverseDecoder.termCheck
  (Continuation20261116.OriginalConcreteHeadSignature.signature 0 arity) allow allow
def input (q : Code (Fin 0)) : List.Vector Nat 4 :=
  List.Vector.ofFn ![typeNumber ground, codeNumber q, numbersNumber [], 0]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic
