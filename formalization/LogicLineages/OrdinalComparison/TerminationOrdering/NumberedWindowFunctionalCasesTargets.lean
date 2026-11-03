module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowBasicCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedOccurrenceTransport NumberedWindowCertificates
def ActualFunctionalAbstraction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (sigma tau : Ty) (f : Head Symbol)
  (ss : Arguments Symbol arity Gamma (headArguments arity f)) (types : List Ty)
  (extras : Arguments Symbol arity Gamma types) (t : MarkedTerm Symbol arity (sigma::Gamma) tau),
  WeakCertificate symbols S above ⟨tau,RecursiveComparison.openMarked f sigma tau ss types extras⟩ ⟨tau,t⟩ →
  WeakCertificate symbols S above ⟨.arrow sigma tau,.marked f (.arrow sigma tau) ss types extras⟩ ⟨.arrow sigma tau,.lam t⟩

def ActualCopy : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  ∀ (Gamma : List Ty) (f g : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
  (types : List Ty) (extras : Arguments Symbol arity Gamma types) (ts : Arguments Symbol arity Gamma (headArguments arity g)),
  RecursiveComparison.headAbove above f g →
  (∀ p∈RecursiveComparison.argumentList ts,WeakCertificate symbols S above ⟨p.1,.marked f p.1 ss types extras⟩ p) →
  WeakCertificate symbols S above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩

def ActualSelect : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (sigma tau : Ty) (f : Head Symbol)
  (ss : Arguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
  (extras : Arguments Symbol arity Gamma extraTypes) (types : List Ty) (q : MarkedTerm Symbol arity Gamma sigma)
  (r t : MarkedTerm Symbol arity Gamma tau) (suffix : sigma=arrows types tau),
  (⟨sigma,q⟩ : OriginalPacked Symbol arity Gamma)∈RecursiveComparison.argumentList ss++RecursiveComparison.argumentList extras →
  applyOriginalWith q (fun v => .var v) (RecursiveComparison.selfArguments f ss extraTypes extras types) suffix=some r →
  WeakCertificate symbols S above ⟨tau,r⟩ ⟨tau,t⟩ →
  WeakCertificate symbols S above ⟨tau,.marked f tau ss extraTypes extras⟩ ⟨tau,t⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowFunctionalCasesTargets
