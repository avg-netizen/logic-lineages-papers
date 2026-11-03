module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportProof

@[expose] public section
/-! Explicit restricted-window induction interfaces. These definitions do not
prove source derivation coverage or discharge final source confinement. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowCertificates
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedFiniteUniverse NumberedWindowTraces NumberedWindowOccurrenceTargets

def OriginalGood {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (q : OriginalPacked Symbol arity Gamma) : Prop :=
  typesAllowed (fun t => t∈S) q.2 ∧ headsAllowed (HeadInWindow arity symbols S) q.2

def GoodList {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (qs : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ q∈qs,InUniverse symbols S q.2

def OriginalGoodList {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (qs : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ q∈qs,OriginalGood symbols S q

def WeakAt {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (s t : OriginalPacked Symbol arity Gamma) : Prop :=
  ∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q → InUniverse symbols S Q → OriginalGood symbols S t →
    ∃ n,WindowTrace Symbol arity symbols S above Gamma n ⟨s.1,Q⟩ (canonicalPacked 0 t)

def WeakCertificate {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (s t : OriginalPacked Symbol arity Gamma) : Prop := ∃ B,WeakAt symbols S above B s t

def StrictAt {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (s t : OriginalPacked Symbol arity Gamma) : Prop :=
  ∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q → InUniverse symbols S Q → OriginalGood symbols S t →
    ∃ (k : Nat) (R : AuxTerm Symbol arity Gamma s.1),finiteMark k Q=some R ∧
      ∃ n,WindowTrace Symbol arity symbols S above Gamma n ⟨s.1,R⟩ (canonicalPacked 0 t)

def StrictCertificate {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (s t : OriginalPacked Symbol arity Gamma) : Prop := ∃ B,StrictAt symbols S above B s t

def MatchAt {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B ss values → GoodList symbols S values → OriginalGoodList symbols S ts → PointwiseWindowTrace symbols S above values (canonicalList 0 ts)

def MatchCertificate {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,MatchAt symbols S above B ss ts

def MultiAt {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B ss values → GoodList symbols S values → OriginalGoodList symbols S ts → ∃ middle,PrimitiveMultiset values middle ∧ PointwiseWindowTrace symbols S above middle (canonicalList 0 ts)

def MultiCertificate {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (ss ts : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,MultiAt symbols S above B ss ts

def ReplacementAt {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (B : Nat) (removed inserted : List (OriginalPacked Symbol arity Gamma)) : Prop :=
  ∀ values,ListRep B removed values → GoodList symbols S values → OriginalGoodList symbols S inserted → ∃ marked,
    (∀ R∈marked,∃ Q∈values,PrimitiveMark Symbol arity Gamma Q R) ∧ PointwiseWindowTrace symbols S above marked (canonicalList 0 inserted)

def ReplacementCertificate {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    {Gamma : List Ty} (removed inserted : List (OriginalPacked Symbol arity Gamma)) : Prop := ∃ B,ReplacementAt symbols S above B removed inserted

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowCertificates
