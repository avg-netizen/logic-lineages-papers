module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowCertificatesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates
def ActualMatchNil : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  MatchCertificate (arity:=arity) symbols S above (Gamma:=Gamma) [] []

def ActualMatchCons : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (s t : OriginalPacked Symbol arity Gamma) (ss ts : List (OriginalPacked Symbol arity Gamma)),
  WeakCertificate symbols S above s t → MatchCertificate symbols S above ss ts →
  MatchCertificate symbols S above (s::ss) (t::ts)

def ActualStrictMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (tau : Ty) (s r t : MarkedTerm Symbol arity Gamma tau),
  RecursiveComparison.strictMark s=some r → WeakCertificate symbols S above ⟨tau,r⟩ ⟨tau,t⟩ →
  StrictCertificate symbols S above ⟨tau,s⟩ ⟨tau,t⟩

def ActualReplacementNil : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ removed : List (OriginalPacked Symbol arity Gamma),ReplacementCertificate symbols S above removed []

def ActualReplacementCons : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (removed : List (OriginalPacked Symbol arity Gamma)) (s t : OriginalPacked Symbol arity Gamma)
  (rest : List (OriginalPacked Symbol arity Gamma)),s∈removed → StrictCertificate symbols S above s t →
  ReplacementCertificate symbols S above removed rest → ReplacementCertificate symbols S above removed (t::rest)

def ActualMultisetReplace : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ ss ts kept retained removed inserted : List (OriginalPacked Symbol arity Gamma),
  ss.Perm (kept++removed) → ts.Perm (retained++inserted) → removed≠[] →
  MatchCertificate symbols S above kept retained → ReplacementCertificate symbols S above removed inserted →
  MultiCertificate symbols S above ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesTargets
