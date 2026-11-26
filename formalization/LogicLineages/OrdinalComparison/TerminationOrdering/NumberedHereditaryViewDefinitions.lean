module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryView
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability
open NumberedPrimarySubstitution
open ID1Completion.SourceComputabilityCompletion

inductive RootSignature (n : Nat) where
 | var (result : Ty) (index : Nat)
 | bottom (result : Ty)
 | lam (domain result : Ty) (body : Ty × Nat)
 | app (domain result : Ty) (function argument : Ty × Nat)
 | ordinary (result : Ty) (head : RecursiveComparison.HeadClass (Fin n)) (base : Multiset (Ty × Nat))
 | numbered (label : Nat) (result : Ty) (head : RecursiveComparison.HeadClass (Fin n))
     (base : Multiset (Ty × Nat)) (extras : List (Ty × Nat))

def typedCode {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
 {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : Ty × Nat :=
 (q.1,representativeCode symbols S q)

def rootSignature {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
 {Gamma : List Ty} : Packed (Fin n) arity Gamma → RootSignature n
 | ⟨tau,.var v⟩ => .var tau (SourceTypedPorts.variableIndex v)
 | ⟨tau,.bottom _⟩ => .bottom tau
 | ⟨_,@AuxTerm.lam _ _ _ sigma tau child⟩ => .lam sigma tau (typedCode symbols S ⟨tau,child⟩)
 | ⟨tau,@AuxTerm.app _ _ _ sigma _ fn arg⟩ => .app sigma tau (typedCode symbols S ⟨.arrow sigma tau,fn⟩) (typedCode symbols S ⟨sigma,arg⟩)
 | ⟨_,.ordinary f args⟩ => .ordinary (headResult f) (RecursiveComparison.headClass f) (argumentCodes symbols S args)
 | ⟨tau,.numbered k f _ args _ extras⟩ => .numbered k tau (RecursiveComparison.headClass f) (argumentCodes symbols S args) (argumentCodes symbols S extras)

/-- Literal typed children, including the extended context of a lambda. -/
inductive Child {n : Nat} {arity : Fin n → Nat} :
 {Gamma : List Ty} → Packed (Fin n) arity Gamma → {Delta : List Ty} → Packed (Fin n) arity Delta → Prop where
 | lam {Gamma sigma tau} (q : AuxTerm (Fin n) arity (sigma::Gamma) tau) :
   Child ⟨.arrow sigma tau,.lam q⟩ ⟨tau,q⟩
 | appFunction {Gamma sigma tau} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma) :
   Child ⟨tau,.app f a⟩ ⟨.arrow sigma tau,f⟩
 | appArgument {Gamma sigma tau} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma) :
   Child ⟨tau,.app f a⟩ ⟨sigma,a⟩
 | ordinary {Gamma} (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
   (q : Packed (Fin n) arity Gamma) : q ∈ argumentList base → Child ⟨headResult f,.ordinary f base⟩ q
 | numberedBase {Gamma} (k : Nat) (f : Head (Fin n)) (tau : Ty)
   (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
   (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) (q : Packed (Fin n) arity Gamma) :
   q ∈ argumentList base → Child ⟨tau,.numbered k f tau base types extras⟩ q
 | numberedExtra {Gamma} (k : Nat) (f : Head (Fin n)) (tau : Ty)
   (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
   (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) (q : Packed (Fin n) arity Gamma) :
   q ∈ argumentList extras → Child ⟨tau,.numbered k f tau base types extras⟩ q

/-- Finite semantic depth only, no numeric fingerprint or runtime selector.
Root BASE permutations and ordered extras determine intended matches; recursive
clauses cover every actual child pair in the same typed class. Every literal
context deletion is visited, including cutoff zero inside lambda bodies. -/
def HereditaryView {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty) :
 Nat → {Gamma : List Ty} → Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop
 | 0, _, q, r => rootSignature symbols S q = rootSignature symbols S r
 | depth+1, Gamma, q, r =>
   rootSignature symbols S q = rootSignature symbols S r ∧
   (∀ (Delta : List Ty) (a b : Packed (Fin n) arity Delta), Child q a → Child r b →
     typedCode symbols S a = typedCode symbols S b → HereditaryView symbols S depth a b) ∧
   (∀ (binders tail : List Ty) (sigma : Ty) (he : Gamma = binders ++ sigma :: tail),
     HereditaryView symbols S depth
       (substitutePacked (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) (he ▸ q))
       (substitutePacked (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) (he ▸ r)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryView
