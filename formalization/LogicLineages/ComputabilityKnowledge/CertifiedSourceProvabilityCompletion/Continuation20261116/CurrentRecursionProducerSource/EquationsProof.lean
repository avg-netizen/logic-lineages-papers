module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

theorem equations {k m : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a baseX base step B G) :
 SourceEquations installed lhs rhs t old a baseX pF pR base step B G R := by
 intro ctx target counter inputs
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 have hf := CurrentCalculationFormulaProgram.StatementChecks.exactInternal 4 p (m+1) (.recursion base step)
  R.producer.formulaTag R.qTag R.SJ.ctag R.SJ.atag R.SJ.ntag
  R.producer.hformula R.hQ R.stepInstallation.hc R.stepInstallation.ha R.stepInstallation.hn ctx target (counter ::ᵥ inputs)
 have hb := CurrentRecursionBaseProgram.StatementChecks.exactInternal 4 p m base B R.BJ R.producer.baseTag
  R.baseInstallation R.producer.hbase ctx target inputs
 have hs := CurrentRecursionStepProgram.StatementChecks.exactInternal 4 p m base step G R.SJ R.producer.stepTag
  R.stepInstallation R.producer.hstep ctx target counter inputs
 have hp := CurrentRecursionProducerProgram.StatementChecks.exactInternalGraph 4 p m base step B G R.producer ctx target counter inputs
 have hz := GorbowPRSymbolicEquations.Proof.recursionZeroEquation 4 p R.qTag m base step R.hQ ctx inputs
 have hsucc := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation 4 p R.qTag m base step R.hQ ctx counter inputs
 exact ⟨GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hf,
  GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hb,
  GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hs,
  GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hp,
  GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hz,
  GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hsucc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.EquationsProof
