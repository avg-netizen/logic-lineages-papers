module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev logical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 UniformClosedRule12.logicalLeaf (CumulativeUniformRule12Registry.previousLogical f lhs rhs old)
abbrev arithmetic (a : Program 1) : Program 1 := RawMulNewestAddition.arithmetic a
abbrev verifier (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) : Program 5 :=
 UniformClosedRule12Certificate.verifier (CumulativeUniformRule12Registry.previousLogical f lhs rhs old)
  (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier f lhs rhs old a baseX)) pR
/-- Entire cumulative carrier and MP fixed before actual tuple/global tag choices. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,CumulativeUniformRule12Registry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩]
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
/-- Exact reinstalled interface in this same newly selected source S. -/
def CompilerCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.previous.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.coreTag I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.previous.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.previous.previous.template.certificateTag values))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def EqualityCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.previous.previous.current.ctag I.previous.previous.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def FullFormulaCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def RetentionCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.coreTag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel context formula code) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def Uniform13Capability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.previous.current.caseTag I.previous.current.predTag I.previous.current.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag formula replacement
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
  (.imp (UniformClosedInstanceRecognizer.guards I.previous.current.fval I.previous.current.vtag formula replacement)
   (.conj (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add C C) code) (.succ .zero))
    (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add C C) code))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def Uniform12Capability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (formula left right index fuel : Term ctx),
 let C := UniformClosedRule12.conclusionValue I.current.caseTag I.current.predTag I.current.ctag formula left right
 let code := UniformClosedRule12Certificate.certificate I.current.ctag I.current.constructorTag formula left right
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
  (.imp (UniformClosedRule12.guards I.current.fval I.current.vtag formula left right)
   (.conj (.equal (LiteralCheckerAcceptance.runCall I.current.iteratorTag I.current.ptag index fuel code)
      (UniformClosedRule12Certificate.output I.current.ptag I.current.ctag I.current.caseTag I.current.predTag formula left right))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source
