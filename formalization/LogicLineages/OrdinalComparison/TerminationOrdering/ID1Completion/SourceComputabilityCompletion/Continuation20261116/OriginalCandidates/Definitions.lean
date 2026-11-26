module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Literal retain/drop step [original candidate, filtered tail, original Gamma].
A successful original typed decoder retains the SAME pair, not a new object. -/
def filterStep (H : Program 1) : Program 3 :=
  InternalAcceptance.branch
    (.composition (OriginalTypedDecoder.packedCheck H) ![.projection 0,.projection 2])
    (.projection 1) (consOf (.projection 0) (.projection 1))
/-- Actual ordered right fold, preserving every repeated successful occurrence.
Inputs are [original classCodes list, Encodable Gamma]. -/
def filterCandidates (H : Program 1) : Program 2 :=
  InternalRawListRecursion.listRec (constant 1 0) (filterStep H)
/-- Original seed/parameter pipeline. Context and typed-seed rejection already
belong to classCodes; no universe guard or invented Object guard is added. -/
def candidates (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Program 2 :=
  .composition (filterCandidates H)
    ![OriginalClassCodes.classCodes n arity H,OriginalClassCodes.gamma]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates
