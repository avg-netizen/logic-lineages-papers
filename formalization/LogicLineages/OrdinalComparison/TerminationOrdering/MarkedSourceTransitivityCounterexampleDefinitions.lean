module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivitySupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexample
open Source Source.SourceMarkedSyntax RecursiveComparison

abbrev arity : Nat → Nat | 0 => 0 | _+1 => 1
def above (f g : Nat) : Prop := g<f
abbrev Ground := MarkedTerm Nat arity [] Ty.ground
def z : Ground := .ordinary (.ranked 0) .nil
def k : Ground := .ordinary (.ranked 1) (by change Arguments Nat arity [] [.ground]; exact .cons z .nil)
def q : Ground := .marked (.ranked 1) .ground (by change Arguments Nat arity [] [.ground]; exact .cons k .nil) [] .nil
def s : Ground := .marked (.ranked 2) .ground (by change Arguments Nat arity [] [.ground]; exact .cons q .nil) [] .nil
def t : Ground := .marked (.ranked 2) .ground (by change Arguments Nat arity [] [.ground]; exact .cons k .nil) [] .nil
def u : Ground := .ordinary (.ranked 2) (by change Arguments Nat arity [] [.ground]; exact .cons z .nil)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexample
