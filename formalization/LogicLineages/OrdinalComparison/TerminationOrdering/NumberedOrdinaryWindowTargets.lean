module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces NumberedOrdinaryWindow
def ActualSourceWindow : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma tau : Ty)
  (s : Term (Fin n) arity Gamma sigma) (t : Term (Fin n) arity Gamma tau),
  SubtypeClosed (fun u => u∈typeWindow s t) ∧
  OriginalGood (symbols n) (typeWindow s t) ⟨sigma,embed s⟩ ∧
  OriginalGood (symbols n) (typeWindow s t) ⟨tau,embed t⟩ ∧
  InUniverse (symbols n) (typeWindow s t) (translateOriginal s) ∧
  InUniverse (symbols n) (typeWindow s t) (translateOriginal t)

def ActualWeakOrdinaryPath : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma tau : Ty)
  (s : Term (Fin n) arity Gamma sigma) (t : Term (Fin n) arity Gamma tau),
  RecursiveComparison.Weak (Fin n) arity above Gamma ⟨sigma,embed s⟩ ⟨tau,embed t⟩ →
  ∃ (m : Nat) (path : WindowTrace (Fin n) arity (symbols n) (typeWindow s t) above Gamma m (translated s) (translated t)),
    allBoundaries path

def ActualStrictOrdinaryPath : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma tau : Ty)
  (s : Term (Fin n) arity Gamma sigma) (t : Term (Fin n) arity Gamma tau),
  RecursiveComparison.Strict (Fin n) arity above Gamma ⟨sigma,embed s⟩ ⟨tau,embed t⟩ →
  ∃ (m : Nat) (_ : 0<m) (path : WindowTrace (Fin n) arity (symbols n) (typeWindow s t) above Gamma m (translated s) (translated t)),
    allBoundaries path

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowTargets
