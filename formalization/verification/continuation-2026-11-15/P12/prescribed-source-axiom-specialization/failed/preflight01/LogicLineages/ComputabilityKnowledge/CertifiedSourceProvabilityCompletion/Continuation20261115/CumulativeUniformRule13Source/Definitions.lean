module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev logical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 UniformClosedRule13.logicalLeaf (CumulativeUniformRule13Registry.previousLogical f lhs rhs old)
abbrev arithmetic (a : Program 1) : Program 1 := RawMulNewestAddition.arithmetic a
abbrev verifier (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) : Program 5 :=
 UniformClosedRule13Certificate.verifier (CumulativeUniformRule13Registry.previousLogical f lhs rhs old)
  (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier f lhs rhs old a baseX)) pR
/-- Entire cumulative carrier and MP fixed before actual tuple/global tag choices. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,CumulativeUniformRule13Registry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩]
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
/-- Exact reinstalled-interface capability in this actual source S. -/
def CompilerCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.coreTag I.previous.previous.previous.consTag I.previous.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.previous.template.certificateTag values))))
/-- Exact reinstalled-interface capability in this actual source S. -/
def EqualityCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled-interface capability in this actual source S. -/
def FullFormulaCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled-interface capability in this actual source S. -/
def RetentionCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.qctag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel context formula code) (.succ .zero))))
def UniformCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 UniformClosedRule13Source.RuntimeCapability (CumulativeUniformRule13Registry.previousLogical f lhs rhs old)
  (arithmetic a) baseX pF pR I.current
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source
