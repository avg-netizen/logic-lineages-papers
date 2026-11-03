module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceProof

@[expose] public section
/-! Typed finite traces are a presentation of the already fixed packed Trace,
not a stronger reduction. Tuple traces use actual ArgumentStep. In particular
there is NO positive reduction lift in an auxiliary application argument.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContexts
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence

inductive TypedTrace (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) : Nat → AuxTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | equivalent {q r} : Primary Symbol arity Gamma ⟨tau,q⟩ ⟨tau,r⟩ → TypedTrace Symbol arity above Gamma tau 0 q r
  | raw {q r} : RawStep Symbol arity above Gamma tau q r → TypedTrace Symbol arity above Gamma tau 1 q r
  | trans {m n q r s} : TypedTrace Symbol arity above Gamma tau m q r → TypedTrace Symbol arity above Gamma tau n r s →
      TypedTrace Symbol arity above Gamma tau (m+n) q s

inductive TupleTrace (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma types : List Ty) : Nat → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | equivalent {base target} : ArgumentPrimary Symbol arity Gamma types base target →
      TupleTrace Symbol arity above Gamma types 0 base target
  | raw {base target} : ArgumentStep Symbol arity above Gamma types base target →
      TupleTrace Symbol arity above Gamma types 1 base target
  | trans {m n base middle target} : TupleTrace Symbol arity above Gamma types m base middle →
      TupleTrace Symbol arity above Gamma types n middle target → TupleTrace Symbol arity above Gamma types (m+n) base target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContexts
