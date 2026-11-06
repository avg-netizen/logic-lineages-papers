module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirect
open Source JointGammaQuotient
abbrev Context (n : Nat) := Parameters n × List Nat

/-- The same original occurrence-index/path witness, with Gamma retained as
an ordinary component of the fixed context for the finite fold. -/
def witness (n : Nat) (arity : Fin n → Nat) (ctx : Context n)
    (y : Nat) (entry : QuotientDominationCertificates.Entry) : Bool :=
  (ctx.2[entry.1]?).any (fun z => NumberedQuotientPathCertificates.positivePathTest n arity
    ctx.1.1.1.1 ctx.1.1.1.2 ctx.1.1.2 ctx.1.2 z y entry.2)

def step (n : Nat) (arity : Fin n → Nat) (ctx : Context n)
    (state : List Nat × Bool) (entry : QuotientDominationCertificates.Entry) : List Nat × Bool :=
  (state.1.tail,state.2 && state.1.head?.any (fun y => witness n arity ctx y entry))

def finish (state : List Nat × Bool) : Bool := decide (state.1 = []) && state.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirect
