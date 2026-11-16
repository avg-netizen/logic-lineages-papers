module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem exactStep : Targets.StepCore := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hstep⟩ := CurrentRecursionStepCertificate.ConstructorProof.exactConstructor
  installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m base step B G R ctx assumptions counter inputs fuel
 dsimp only
 intro hguard hchild
 obtain ⟨haccepted⟩ := hstep m base step R.qTag R.hQ ctx assumptions counter inputs
  (call R.qTag (counter ::ᵥ inputs))
  (call (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs))
  (childCode R.GTag (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag counter inputs)) fuel hguard hchild
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) haccepted
 obtain ⟨hprior⟩ := FormulaBridge.actualFormula p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨hnext⟩ := FormulaBridge.successor p installed lhs rhs t old a baseX I base step B G R counter inputs
 obtain ⟨hformula⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 7
  I.previous.current.h_ctag I.previous.current.h_atag I.previous.current.h_ctag I.previous.current.h_atag
  _ _ _ _ hprior hnext
 obtain ⟨hformulaU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hformula⟩
 obtain ⟨hformulaCore⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hformulaU) hcore
 obtain ⟨hgraph⟩ := CurrentRecursionStepProgram.StatementChecks.exactInternal _ p m base step G R.SJ R.producer.stepTag
  R.stepInstallation R.producer.hstep ctx (Term.numeral R.qTag) counter inputs
 obtain ⟨hvalue⟩ := StepCode.value p installed lhs rhs t old a baseX I base step B G R counter inputs
 have hcode := Logic.trans _ _ _ hgraph hvalue
 obtain ⟨hcodeU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hcode⟩
 exact CurrentImplicationCertificate.RebaseProof.coreCode U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hcodeU) hformulaCore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepProof
