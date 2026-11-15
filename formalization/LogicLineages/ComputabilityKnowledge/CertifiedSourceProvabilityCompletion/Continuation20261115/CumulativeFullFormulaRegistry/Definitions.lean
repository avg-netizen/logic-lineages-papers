module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev previousLogical (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 CumulativeInstantiationSource.logical lhs rhs old
/-- Entire old finite registry, including all23 interfaces and template compiler,
plus actual full-formula package. All ASTs fixed before tags/runtime values. -/
def items {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : List Packed :=
 CumulativeInstantiationRegistry.items lhs rhs t old a x ++
 FullFormulaInstantiationRegistry.items f (previousLogical lhs rhs old) (RawMulNewestAddition.arithmetic a) x
def carrier {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items f lhs rhs t old a x)
structure JointInstallation {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) where
 previous : CumulativeInstantiationRegistry.JointInstallation p lhs rhs t old a x
 current : FullFormulaInstantiationCertificate.Installation p f (previousLogical lhs rhs old) (RawMulNewestAddition.arithmetic a) x
/-- These capabilities are parametrized by the ACTUAL registry root, so future
published source admission must rebuild root-global memberships before reuse. -/
def CompilerCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.qctag I.previous.previous.consTag I.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.template.certificateTag values))))
def EqualityCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)) (.succ .zero))))
def FullFormulaCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.current.ctag I.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.current.ctag I.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.current.ctag I.current.qtag raw)) (.succ .zero))))
def RetentionCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.qctag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel context formula code) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry
