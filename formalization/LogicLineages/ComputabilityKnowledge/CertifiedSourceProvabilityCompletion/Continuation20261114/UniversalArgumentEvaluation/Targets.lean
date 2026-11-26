module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
/-- Actual original arithmetic compiler retained at distinct new checker. -/
def InternalArithmetic : Prop := ∀ k (t : Term k), ArithmeticTemplateEvaluation.Arithmetic t →
 ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (J : ArithmeticTemplateEvaluation.TemplateInstallation p t),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.conj (RawReflexivityDispatcher.valid I.validatorTag (call J.quoteTag values))
  (RawEqualityComposition.accepted I.universalCoreTag I.consTag I.appendTag index fuel
   (call J.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (call J.certificateTag values))))
/-- Original token5 argument reduction only. Universal function value is NOT evaluated. -/
def InternalUniversalArgument : Prop := ∀ k (t : Term k), ArithmeticTemplateEvaluation.Arithmetic t →
 ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (J : ArithmeticTemplateEvaluation.TemplateInstallation p t),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (RawEqualityComposition.accepted I.universalCoreTag I.consTag I.appendTag index fuel
  (RawUniversalReplace.universalValue I.consTag (call J.quoteTag values))
  (RawUniversalReplace.universalValue I.consTag
   (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values)))
  (certificate I.mpTag I.universalLineTag I.reflexivityTag I.consTag I.appendTag I.numeralTag J.quoteTag J.certificateTag t values)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Targets
