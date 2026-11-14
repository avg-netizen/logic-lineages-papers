module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
/-- For each fixed ORIGINAL arithmetic template, the actual compiled value
program computes the original symbolic substitution, for every runtime vector. -/
def InternalValue : Prop := ∀ k (t : Term k), Arithmetic t →
 ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (J : TemplateInstallation p t),
 ∀ ctx (values : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call J.valueTag values) (instantiatedValue t values)))
/-- Genuine structural compiler correctness, with the same checker fixed before
all runtime values/index/fuel. The actual compiled certificate CALL is checked.
No operand-success, external model truth, or raw-parser oracle is a premise. -/
def InternalEvaluation : Prop := ∀ k (t : Term k), Arithmetic t →
 ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (J : TemplateInstallation p t),
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj (RawReflexivityDispatcher.valid I.validatorTag (call J.quoteTag values))
   (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
    (call J.quoteTag values)
    (LiteralNumeralPrefix.numeralCall I.numeralTag (instantiatedValue t values))
    (call J.certificateTag values))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.Targets
