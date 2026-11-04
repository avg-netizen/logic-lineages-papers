module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilityTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedBottomSpine

def ActualBottomSpineLeast : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q → BottomSpine q →
    representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩ ∈ leastSet scalar context

def ActualBottomSpineComputable : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q → BottomSpine q →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context)
      context tau (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

def ActualBottomComputable : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ tau : Ty, tau ∈ ctx.1.2 →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context)
      context tau (representativeCode ctx.1.1 ctx.1.2 (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilityTargets
