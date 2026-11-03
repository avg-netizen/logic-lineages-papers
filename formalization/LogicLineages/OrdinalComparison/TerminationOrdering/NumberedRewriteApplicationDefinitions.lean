module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkProof

@[expose] public section
/-! Finite raw auxiliary paths and literal typed argument concatenation.
Actual auxiliary applications associate by their syntax. NO currying law for
the ORIGINAL special application is asserted or used. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplication
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

inductive RawSteps (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) : AuxTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | refl (q : AuxTerm Symbol arity Gamma tau) : RawSteps Symbol arity above Gamma tau q q
  | next (q r s : AuxTerm Symbol arity Gamma tau) : RawStep Symbol arity above Gamma tau q r →
      RawSteps Symbol arity above Gamma tau r s → RawSteps Symbol arity above Gamma tau q s

abbrev ExtraTuple (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :=
  Sigma (AuxArguments Symbol arity Gamma)

def appendTuple {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (a b : ExtraTuple Symbol arity Gamma) : ExtraTuple Symbol arity Gamma :=
  ⟨a.1++b.1,NumberedRewriteSyntax.appendArguments a.2 b.2⟩

def prependTuple {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma : Ty}
    (q : AuxTerm Symbol arity Gamma sigma) (a : ExtraTuple Symbol arity Gamma) : ExtraTuple Symbol arity Gamma :=
  ⟨sigma::a.1,.cons q a.2⟩

def numberedFromTuple {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (f : Head Symbol) (tau : Ty) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (a : ExtraTuple Symbol arity Gamma) : AuxTerm Symbol arity Gamma tau :=
  .numbered n f tau base a.1 a.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplication
