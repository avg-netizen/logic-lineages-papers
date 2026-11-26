module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaTargets
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound
def DepthTrace : Prop := ∀ n c depth (a : Job n) (suffix : List (Frame n)),
 FrontierTerminal depth a → Trace c (2 * visits depth a.core) (Frame.visit a :: suffix) suffix
def BoundedTrace : Prop := ∀ n c (a : Job n) (suffix : List (Frame n)),
 ∃ steps, steps = 2 * totalWork a.core ∧
 steps ≤ 2 * budget (weight a.core + 2) (weight a.core) ∧
 Trace c steps (Frame.visit a :: suffix) suffix
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaTargets
