module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTraces
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseOperationsTargets NumberedWindowReduction NumberedWindowEquivalence

inductive WindowTrace (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) : Nat → Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | equivalent {q r} : WindowPrimary Symbol arity symbols S Gamma q r → WindowTrace Symbol arity symbols S above Gamma 0 q r
  | raw {tau} (q r : AuxTerm Symbol arity Gamma tau) : WindowStep Symbol arity symbols S above Gamma tau q r →
      WindowTrace Symbol arity symbols S above Gamma 1 ⟨tau,q⟩ ⟨tau,r⟩
  | trans {m n q r s} : WindowTrace Symbol arity symbols S above Gamma m q r →
      WindowTrace Symbol arity symbols S above Gamma n r s → WindowTrace Symbol arity symbols S above Gamma (m+n) q s

inductive WindowTypedTrace (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) : Nat → AuxTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | equivalent {q r} : WindowPrimary Symbol arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩ → WindowTypedTrace Symbol arity symbols S above Gamma tau 0 q r
  | raw {q r} : WindowStep Symbol arity symbols S above Gamma tau q r → WindowTypedTrace Symbol arity symbols S above Gamma tau 1 q r
  | trans {m n q r s} : WindowTypedTrace Symbol arity symbols S above Gamma tau m q r → WindowTypedTrace Symbol arity symbols S above Gamma tau n r s →
      WindowTypedTrace Symbol arity symbols S above Gamma tau (m+n) q s

inductive WindowTupleTrace (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma types : List Ty) : Nat → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | equivalent {base target} : WindowArgumentPrimary Symbol arity symbols S Gamma types base target →
      WindowTupleTrace Symbol arity symbols S above Gamma types 0 base target
  | raw {base target} : WindowArgumentStep Symbol arity symbols S above Gamma types base target →
      WindowTupleTrace Symbol arity symbols S above Gamma types 1 base target
  | trans {m n base middle target} : WindowTupleTrace Symbol arity symbols S above Gamma types m base middle →
      WindowTupleTrace Symbol arity symbols S above Gamma types n middle target → WindowTupleTrace Symbol arity symbols S above Gamma types (m+n) base target

/-- Actual boundary occurrence in a trace, including each composition junction. -/
inductive Boundary {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} :
    {n : Nat} → {q r : Packed Symbol arity Gamma} → WindowTrace Symbol arity symbols S above Gamma n q r → Packed Symbol arity Gamma → Prop where
  | start {n q r} (h : WindowTrace Symbol arity symbols S above Gamma n q r) : Boundary h q
  | finish {n q r} (h : WindowTrace Symbol arity symbols S above Gamma n q r) : Boundary h r
  | left {m n q r s p} (h : WindowTrace Symbol arity symbols S above Gamma m q r)
      (k : WindowTrace Symbol arity symbols S above Gamma n r s) : Boundary h p → Boundary (.trans h k) p
  | right {m n q r s p} (h : WindowTrace Symbol arity symbols S above Gamma m q r)
      (k : WindowTrace Symbol arity symbols S above Gamma n r s) : Boundary k p → Boundary (.trans h k) p

inductive TupleBoundary {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma types : List Ty} :
    {n : Nat} → {a b : AuxArguments Symbol arity Gamma types} → WindowTupleTrace Symbol arity symbols S above Gamma types n a b → AuxArguments Symbol arity Gamma types → Prop where
  | start {n a b} (h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b) : TupleBoundary h a
  | finish {n a b} (h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b) : TupleBoundary h b
  | left {m n a b c p} (h : WindowTupleTrace Symbol arity symbols S above Gamma types m a b)
      (k : WindowTupleTrace Symbol arity symbols S above Gamma types n b c) : TupleBoundary h p → TupleBoundary (.trans h k) p
  | right {m n a b c p} (h : WindowTupleTrace Symbol arity symbols S above Gamma types m a b)
      (k : WindowTupleTrace Symbol arity symbols S above Gamma types n b c) : TupleBoundary k p → TupleBoundary (.trans h k) p

def allBoundaries {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {n : Nat} {q r : Packed Symbol arity Gamma}
    (h : WindowTrace Symbol arity symbols S above Gamma n q r) : Prop :=
  ∀ p, Boundary h p → PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) p

def allTupleBoundaries {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma types : List Ty} {n : Nat} {a b : AuxArguments Symbol arity Gamma types}
    (h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b) : Prop :=
  ∀ p, TupleBoundary h p → GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) p

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTraces
