module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteReductionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

/-- A genuine single positive numbered reduction for the literal ORIGINAL
partial mark, including an arbitrary initial lambda spine. -/
def ActualRawPositiveMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (q r : MarkedTerm Symbol arity Gamma tau),RecursiveComparison.strictMark q=some r →
    ∀ Q : AuxTerm Symbol arity Gamma tau,Represents Symbol arity (n+1) Gamma tau q Q →
    ∃ R,RawStep Symbol arity above Gamma tau Q R ∧ Represents Symbol arity n Gamma tau r R

def ActualOrdinaryPositiveMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (q : Term Symbol arity Gamma tau) (r : MarkedTerm Symbol arity Gamma tau),
    RecursiveComparison.strictMark (embed q)=some r →
    ∃ R,RawStep Symbol arity above Gamma tau (translateOriginal q) R ∧ Represents Symbol arity n Gamma tau r R

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkTargets
