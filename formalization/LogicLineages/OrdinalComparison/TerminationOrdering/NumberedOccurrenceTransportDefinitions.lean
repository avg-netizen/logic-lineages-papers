module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityProof

@[expose] public section
/-! Occurrence-preserving representations. Permutation transport must move
the ACTUAL auxiliary occurrences, not replace marked representations by an
arbitrary canonical representative. Typed-vector reconstruction is exact.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransport
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence

abbrev OriginalPacked (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :=
  RecursiveComparison.Packed Symbol arity Gamma

def PackedRep {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (n : Nat)
    (q : OriginalPacked Symbol arity Gamma) (Q : Packed Symbol arity Gamma) : Prop :=
  ∃ A : AuxTerm Symbol arity Gamma q.1,Q=⟨q.1,A⟩ ∧ Represents Symbol arity n Gamma q.1 q.2 A

def ListRep {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (n : Nat)
    (qs : List (OriginalPacked Symbol arity Gamma)) (values : List (Packed Symbol arity Gamma)) : Prop :=
  List.Forall₂ (PackedRep n) qs values

def PointwiseTrace {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (qs rs : List (Packed Symbol arity Gamma)) : Prop :=
  List.Forall₂ (fun q r => ∃ n,Trace Symbol arity above Gamma n q r) qs rs

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransport
