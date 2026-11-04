module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths SourceFreshBodyAccessibility

def ActualFreshBodyIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma :: Gamma) tau), freshInstance body = body

def ActualFreshBodyAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalar context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ (tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
    SourceComputabilityFormula.Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,freshInstance body⟩) →
    Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma :: Gamma)) source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,body⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibilityTargets
