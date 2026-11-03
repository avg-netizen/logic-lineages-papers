module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces
def ActualWeakSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ s t : OriginalPacked Symbol arity Gamma,RecursiveComparison.Weak Symbol arity above Gamma s t → WeakCertificate symbols S above s t

def ActualStrictInitialMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ s t : OriginalPacked Symbol arity Gamma,RecursiveComparison.Strict Symbol arity above Gamma s t → StrictCertificate symbols S above s t

def ActualStrictSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ s t : OriginalPacked Symbol arity Gamma,RecursiveComparison.Strict Symbol arity above Gamma s t →
  ∃ B,∀ Q : AuxTerm Symbol arity Gamma s.1,Represents Symbol arity B Gamma s.1 s.2 Q →
    InUniverse symbols S Q → OriginalGood symbols S t →
    ∃ n,0<n ∧ WindowTrace Symbol arity symbols S above Gamma n ⟨s.1,Q⟩ (canonicalPacked 0 t)

def ActualMatchSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ ss ts : List (OriginalPacked Symbol arity Gamma),RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts → MatchCertificate symbols S above ss ts

def ActualMultisetSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ ss ts : List (OriginalPacked Symbol arity Gamma),RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts → MultiCertificate symbols S above ss ts

def ActualReplacementSimulation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty),
  ∀ ss ts : List (OriginalPacked Symbol arity Gamma),RecursiveComparison.ReplacementMatch Symbol arity above Gamma ss ts → ReplacementCertificate symbols S above ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationTargets
