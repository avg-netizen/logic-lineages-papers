module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationDefinitions

@[expose] public section
/-! FULL one-way RAW simulation of the five literal original inductive
relations, with their genuine existential finite common budget. Strict proofs
must start by a real primitive mark; permutation/equivalence motion alone is
not positive. No transitivity/stability of the original relation is assumed.
These targets are still COMPONENTS of source lem:simulation until fixed-S
confinement, least-code quotient and computable translation are proved.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation

def ActualWeakSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : OriginalPacked Symbol arity Gamma),RecursiveComparison.Weak Symbol arity above Gamma s t →
    ∃ B,∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
      ∃ n,Trace Symbol arity above Gamma n ⟨s.1,Q⟩ (canonicalPacked 0 t)

def ActualStrictInitialMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : OriginalPacked Symbol arity Gamma),RecursiveComparison.Strict Symbol arity above Gamma s t →
    ∃ B,∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
      ∃ (k : Nat) (R : AuxTerm Symbol arity Gamma s.1),finiteMark k Q=some R ∧
        ∃ n,Trace Symbol arity above Gamma n ⟨s.1,R⟩ (canonicalPacked 0 t)

def ActualStrictSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : OriginalPacked Symbol arity Gamma),RecursiveComparison.Strict Symbol arity above Gamma s t →
    ∃ B,∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
      ∃ n,0<n ∧ Trace Symbol arity above Gamma n ⟨s.1,Q⟩ (canonicalPacked 0 t)

def ActualMatchSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (ss ts : List (OriginalPacked Symbol arity Gamma)),RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts →
    ∃ B,∀ values,ListRep B ss values → PointwiseTrace above values (canonicalList 0 ts)

def ActualMultisetSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (ss ts : List (OriginalPacked Symbol arity Gamma)),RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts →
    ∃ B,∀ values,ListRep B ss values → ∃ middle,
      PrimitiveMultiset values middle ∧ PointwiseTrace above middle (canonicalList 0 ts)

def ActualReplacementSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (removed inserted : List (OriginalPacked Symbol arity Gamma)),
    RecursiveComparison.ReplacementMatch Symbol arity above Gamma removed inserted →
    ∃ B,∀ values,ListRep B removed values → ∃ marked,
      (∀ R∈marked,∃ Q∈values,PrimitiveMark Symbol arity Gamma Q R) ∧
        PointwiseTrace above marked (canonicalList 0 inserted)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationTargets
