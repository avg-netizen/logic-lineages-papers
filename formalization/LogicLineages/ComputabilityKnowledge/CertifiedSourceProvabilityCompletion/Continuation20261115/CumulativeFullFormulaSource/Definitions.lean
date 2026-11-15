module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev logical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 FullFormulaInstantiation.logicalLeaf f (CumulativeFullFormulaRegistry.previousLogical lhs rhs old)
abbrev arithmetic (a : Program 1) : Program 1 := RawMulNewestAddition.arithmetic a
abbrev verifier (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) : Program 5 :=
 FullFormulaInstantiationCertificate.verifier f (CumulativeFullFormulaRegistry.previousLogical lhs rhs old)
  (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier f lhs rhs old a baseX)) pR
/-- Noncircular extra AST chosen before source tuple/tag witnesses. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,CumulativeFullFormulaRegistry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩]
/-- All six original published-source packages at the SAME new tuple/leaves. -/
def Packages (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := logical f lhs rhs old
 let ar := arithmetic a
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l ar x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l ar x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l ar x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l ar baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l ar baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l ar baseX pF pR c
def CompilerCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (pF pR : Program 1)
 (I : CumulativeFullFormulaRegistry.JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a x))
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.qctag I.previous.previous.consTag I.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.template.certificateTag values))))
def EqualityCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (pF pR : Program 1)
 (I : CumulativeFullFormulaRegistry.JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a x))
 (.imp (RawReflexivityDispatcher.valid I.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)) (.succ .zero))))
def FullFormulaCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (pF pR : Program 1)
 (I : CumulativeFullFormulaRegistry.JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a x))
 (.imp (RawReflexivityDispatcher.valid I.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.current.ctag I.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.current.ctag I.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.current.ctag I.current.qtag raw)) (.succ .zero))))
def RetentionCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (pF pR : Program 1)
 (I : CumulativeFullFormulaRegistry.JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a x))
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.qctag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel context formula code) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource
