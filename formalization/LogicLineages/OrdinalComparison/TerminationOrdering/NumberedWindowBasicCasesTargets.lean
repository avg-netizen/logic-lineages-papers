module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates
def ActualVariable : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (tau : Ty) (v : Variable Gamma tau),WeakCertificate (arity:=arity) symbols S above ⟨tau,.var v⟩ ⟨tau,.var v⟩

def ActualAbstraction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (sigma tau : Ty) (s t : MarkedTerm Symbol arity (sigma::Gamma) tau),
  WeakCertificate symbols S above ⟨tau,s⟩ ⟨tau,t⟩ →
  WeakCertificate symbols S above ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩

def ActualFunction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
  (ts : Arguments Symbol arity Gamma (headArguments arity g)) (matched : List (OriginalPacked Symbol arity Gamma)),
  RecursiveComparison.headEquivalent f g → headResult f=headResult g → (RecursiveComparison.argumentList ts).Perm matched →
  MatchCertificate symbols S above (RecursiveComparison.argumentList ss) matched →
  WeakCertificate symbols S above ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩

def ActualPut : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (f : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
  (t : MarkedTerm Symbol arity Gamma (headResult f)),
  WeakCertificate symbols S above ⟨headResult f,.marked f (headResult f) ss [] .nil⟩ ⟨headResult f,t⟩ →
  WeakCertificate symbols S above ⟨headResult f,.ordinary f ss⟩ ⟨headResult f,t⟩

def ActualStatus : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty),
  ∀ (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
  (types : List Ty) (extras : Arguments Symbol arity Gamma types) (ts : Arguments Symbol arity Gamma (headArguments arity g)),
  RecursiveComparison.headEquivalent f g →
  MultiCertificate symbols S above (RecursiveComparison.argumentList ss) (RecursiveComparison.argumentList ts) →
  WeakCertificate symbols S above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesTargets
