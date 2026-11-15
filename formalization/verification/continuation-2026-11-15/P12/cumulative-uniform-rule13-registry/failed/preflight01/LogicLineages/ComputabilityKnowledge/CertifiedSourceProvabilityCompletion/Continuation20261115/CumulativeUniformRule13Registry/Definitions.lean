module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev previousLogical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 CumulativeFullFormulaSource.logical f lhs rhs old
/-- Entire prior registry preserved literally, followed by new26AST package.
All programs fixed before global tags or runtime inputs; no self-tag reference. -/
def items {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : List Packed :=
 CumulativeFullFormulaRegistry.items f lhs rhs t old a x ++
 UniformClosedRule13Registry.items (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
def carrier {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items f lhs rhs t old a x)
structure JointInstallation {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) where
 previous : CumulativeFullFormulaRegistry.JointInstallation p f lhs rhs t old a x
 current : UniformClosedRule13Certificate.Installation p (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
/-- Actual-root capabilities preserve original source terms, quotation validity
and exact certificate codes; only the receiving checker changes. -/
def CompilerCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.coreTag I.previous.previous.previous.consTag I.previous.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.previous.template.certificateTag values))))
def EqualityCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)) (.succ .zero))))
def FullFormulaCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)) (.succ .zero))))
def RetentionCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.qctag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel context formula code) (.succ .zero))))
def UniformCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 UniformClosedRule13Registry.RuntimeCapability p (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.current
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry
