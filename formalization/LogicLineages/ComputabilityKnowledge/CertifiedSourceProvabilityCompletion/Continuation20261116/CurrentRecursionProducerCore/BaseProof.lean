module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem exactBase : Targets.BaseCore := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hbase⟩ := CumulativePropositionalSource.NewRecursionBaseConstructorProof.exactConstructor
  installed lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m base step B G R ctx assumptions inputs fuel
 dsimp only
 intro hguard hchild
 obtain ⟨haccepted⟩ := hbase m base step R.qTag R.hQ ctx assumptions inputs
  (call (R.qTag+1) inputs) (childCode R.BTag (R.qTag+1) inputs) fuel hguard hchild
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) haccepted
 obtain ⟨hformula⟩ := FormulaBridge.zero p installed lhs rhs t old a baseX I base step B G R inputs
 obtain ⟨hformulaU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ (Logic.symm _ _ hformula)
 obtain ⟨hformulaCore⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hformulaU) hcore
 obtain ⟨hgraph⟩ := CurrentRecursionBaseProgram.StatementChecks.exactInternal _ p m base B R.BJ R.producer.baseTag
  R.baseInstallation R.producer.hbase ctx (Term.numeral R.qTag) inputs
 obtain ⟨hvalue⟩ := BaseCode.value p installed lhs rhs t old a baseX I base step B G R inputs
 have hcode := Logic.trans _ _ _ hgraph hvalue
 obtain ⟨hcodeU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ (Logic.symm _ _ hcode)
 exact CurrentImplicationCertificate.RebaseProof.coreCode U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hcodeU) hformulaCore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseProof
