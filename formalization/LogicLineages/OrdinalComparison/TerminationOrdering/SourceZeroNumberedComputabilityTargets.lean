module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceZeroNumberedComputability

def ActualZeroNumberedStep : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (f : Head Symbol) (tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) (r : AuxTerm Symbol arity Gamma tau),
  WindowStep Symbol arity symbols S above Gamma tau (.numbered 0 f tau base types extras) r ↔
    r = .bottom tau ∨
    (∃ target, WindowArgumentStep Symbol arity symbols S above Gamma (headArguments arity f) base target ∧
      r = .numbered 0 f tau target types extras) ∨
    (∃ target, WindowArgumentStep Symbol arity symbols S above Gamma types extras target ∧
      r = .numbered 0 f tau base types target)

def ActualPrimaryNumberedMembers : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → WindowPrimary (Fin n) arity symbols S Gamma q r →
    numberedLabel q = numberedLabel r ∧
    (numberedMembers symbols S q).Perm (numberedMembers symbols S r)

def ActualZeroNumberedEdge : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) (y : Nat),
    InUniverse symbols S (.numbered 0 f tau base types extras) →
    QuotientEdge n arity symbols S above Gamma
      (representativeCode symbols S ⟨tau,.numbered 0 f tau base types extras⟩) y →
    y = representativeCode symbols S (⟨tau,.bottom tau⟩ : Packed (Fin n) arity Gamma) ∨
    ∃ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g))
      (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      InUniverse symbols S (.numbered 0 g tau base' types' extras') ∧
      y = representativeCode symbols S ⟨tau,.numbered 0 g tau base' types' extras'⟩ ∧
      OneMemberReplacement n arity symbols S above Gamma
        (argumentCodes symbols S base ++ argumentCodes symbols S extras)
        (argumentCodes symbols S base' ++ argumentCodes symbols S extras')

def ActualZeroNumberedComputable : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types),
    InUniverse ctx.1.1 ctx.1.2 (.numbered 0 f tau base types extras) →
    (∀ p ∈ argumentList base ++ argumentList extras,
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context p.1
        (representativeCode ctx.1.1 ctx.1.2 p)) →
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.numbered 0 f tau base types extras⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityTargets
