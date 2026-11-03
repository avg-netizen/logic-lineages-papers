module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportProof

@[expose] public section
/-! Internal induction invariants for the FROZEN full simulation contract.
Conditional constructor lemmas are not the full theorem: actual source
induction must supply every one of their certificate premises.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationCertificates
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation

def WeakAt {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (s t : OriginalPacked Symbol arity Gamma) : Prop :=
  ∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
    ∃ n,Trace Symbol arity above Gamma n ⟨s.1,Q⟩ (canonicalPacked 0 t)

def WeakCertificate {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (s t : OriginalPacked Symbol arity Gamma) : Prop := ∃ B,WeakAt above B s t

def StrictAt {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (s t : OriginalPacked Symbol arity Gamma) : Prop :=
  ∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
    ∃ (k : Nat) (R : AuxTerm Symbol arity Gamma s.1),finiteMark k Q=some R ∧
      ∃ n,Trace Symbol arity above Gamma n ⟨s.1,R⟩ (canonicalPacked 0 t)

def StrictCertificate {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (s t : OriginalPacked Symbol arity Gamma) : Prop := ∃ B,StrictAt above B s t

def MatchAt {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B ss values → PointwiseTrace above values (canonicalList 0 ts)

def MatchCertificate {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,MatchAt above B ss ts

def MultiAt {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B ss values → ∃ middle,PrimitiveMultiset values middle ∧ PointwiseTrace above middle (canonicalList 0 ts)

def MultiCertificate {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,MultiAt above B ss ts

def ReplacementAt {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (removed inserted : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B removed values → ∃ marked,
    (∀ R∈marked,∃ Q∈values,PrimitiveMark Symbol arity Gamma Q R) ∧ PointwiseTrace above marked (canonicalList 0 inserted)

def ReplacementCertificate {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (removed inserted : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,ReplacementAt above B removed inserted

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationCertificates
