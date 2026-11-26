module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- The original symbol list in the unchanged outer Context = Window × table. -/
def contextSymbols : Program 1 := .composition InternalUnpair.left (fun _ : Fin 1 => InternalUnpair.left)
/-- Literal original raw window, with actual Context product selectors. This
component alone is NOT the original allraw decoded headWindowValue. -/
def rawWindow (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition (Continuation20261114.OriginalHeadWindow.window n arity)
    ![.projection 0,
      .composition contextSymbols (fun _ : Fin 1 => .projection 1),
      .composition OriginalUniverseDomainCoverage.contextTypes (fun _ : Fin 1 => .projection 1)]
/-- Actual original decoded W realization: malformed Context and head reject,
including basic nonzero payloads and ranked symbols outside Fin n. -/
def window (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  InternalAcceptance.conjunction
    (.composition (Continuation20261115.OriginalDecodedContextValidity.contextGuard n)
      (fun _ : Fin 1 => .projection 1))
    (InternalAcceptance.conjunction
      (.composition (Continuation20261115.OriginalHeadDecoderValidity.check n)
        (fun _ : Fin 1 => .projection 0))
      (rawWindow n arity))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage
