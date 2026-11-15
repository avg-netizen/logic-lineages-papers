module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.RegistryItems
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The full paid arithmetic/template/universal-congruence logical prefix. -/
abbrev previousLogical (old : Program 1) : Program 1 :=
 RawUniversalReplace.logicalLeaf (RawUniversalCongruence.previousLogical old)
/-- All literal fields of both inherited installation trees, plus the fixed
arithmetic template compiler. This list is fixed before any runtime values. -/
def items {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3) : List Packed :=
 Items_RawUniversalCongruence.items old a x ++
 Items_RawEqualityInstantiationCertificate.items lhs rhs (previousLogical old) (RawMulNewestAddition.arithmetic a) x ++
 [⟨k,LiteralTemplateQuote.templateQuote t⟩,
  ⟨k,ArithmeticTemplateEvaluation.valueProgram t⟩,
  ⟨k,ArithmeticTemplateEvaluation.certificateProgram t⟩]
/-- Concrete finite syntactic carrier, not an evaluator oracle or published source. -/
def carrier {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items lhs rhs t old a x)
structure JointInstallation {n k : Nat} (p : Program n) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) where
 previous : RawUniversalCongruence.Installation p old a x
 template : ArithmeticTemplateEvaluation.TemplateInstallation p t
 current : RawEqualityInstantiationCertificate.Installation p lhs rhs (previousLogical old) (RawMulNewestAddition.arithmetic a) x
/-- Actual unchanged arithmetic certificate program checked by the new CORE. -/
def CompilerCapability {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (carrier lhs rhs t old a x))
 (.conj (RawReflexivityDispatcher.valid I.previous.validatorTag (GorbowPRDefiningEquations.call I.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.qctag I.previous.consTag I.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.template.certificateTag values))))
/-- Literal fixed-tag13 singleton certificate at the same selected new CORE. -/
def InstantiationCapability {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (carrier lhs rhs t old a x))
 (.imp (RawReflexivityDispatcher.valid I.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.current.ctag I.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.current.ctag I.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.current.ctag I.current.qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry
