module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.GuardBound
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorInstallation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

open GorbowSubstitution GorbowFormulaSubstitution
theorem exactAccumulator : Targets.AccumulatorCore := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨baseFuel,hbase⟩ := BaseProof.exactBase installed lhs rhs k t old a baseX pF pR c hA hn I
 obtain ⟨stepFuel,hstep⟩ := StepProof.exactStep installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨baseFuel+stepFuel,?_⟩
 intro m base step B G R ctx inputs fuel counter
 dsimp only
 intro hguard hbaseChild hstepChild
 obtain ⟨hguard⟩ := hguard
 obtain ⟨hbLower⟩ := GuardBound.lowerAdd U baseFuel stepFuel fuel
 have hbGuard := Derivation.mp hbLower hguard
 obtain ⟨hsLower⟩ := GuardBound.lowerAdd U stepFuel baseFuel fuel
 have hsGuard : Derivation U (orderGuard (Term.numeral stepFuel) fuel) := by
  rw [Nat.add_comm stepFuel baseFuel] at hsLower
  exact .mp hsLower hguard
 obtain ⟨hsLift⟩ := GorbowDerivationSubstitution.Proof.derivationSubstitution U ctx (ctx+1)
  (orderGuard (Term.numeral stepFuel) fuel) (fun i => Term.var i.succ) ⟨hsGuard⟩
 have hsLift' : Derivation U (orderGuard (Term.numeral (n := ctx+1) stepFuel) (liftTerm fuel)) := by
  simpa only [FuelWitness.ExtractionLogicProof.substOrder,Logic.substNumeral,liftTerm,renameTerm] using hsLift
 obtain ⟨A,hATag,hBTag⟩ := AccumulatorInstallation.installed p installed lhs rhs t old a baseX base step B G R
 obtain ⟨hbaseChild⟩ := hbaseChild
 obtain ⟨hb⟩ := hbase m base step B G R ctx [] inputs fuel ⟨.base hbGuard⟩ ⟨.base hbaseChild⟩
 obtain ⟨hbf⟩ := AccumulatorInstallation.formulaGraph p installed lhs rhs t old a baseX base step B G R A .zero inputs
 obtain ⟨hbfU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hbf⟩
 obtain ⟨hb'⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hbfU) hb
 have hbFinal := Hilbert.Local.finish hb'
 rw [← hBTag] at hbFinal
 let liftedInputs := inputs.map liftTerm
 obtain ⟨hstepChild⟩ := hstepChild
 have hstepChild' : Hilbert.Local U (ctx+1) []
  (core I.currentK.coreTag (Term.numeral (Encodable.encode c)) (liftTerm fuel)
   (childFormula J (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag (.var 0) liftedInputs))
   (childCode R.GTag (R.qTag+GorbowPRChildTags.stepTag base) (stepInputs R.qTag (.var 0) liftedInputs))) := by
  simpa only [liftTerm,renameTerm,Logic.substNumeral,liftedInputs] using (Hilbert.Local.base (Gamma := []) hstepChild)
 obtain ⟨hs⟩ := hstep m base step B G R (ctx+1) [] (.var 0) liftedInputs (liftTerm fuel) ⟨.base hsLift'⟩ ⟨hstepChild'⟩
 obtain ⟨hpf⟩ := AccumulatorInstallation.formulaGraph p installed lhs rhs t old a baseX base step B G R A (.var 0) liftedInputs
 obtain ⟨hnf⟩ := AccumulatorInstallation.formulaGraph p installed lhs rhs t old a baseX base step B G R A (.succ (.var 0)) liftedInputs
 obtain ⟨hif⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 7
  I.previous.current.h_ctag I.previous.current.h_atag I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hpf hnf
 obtain ⟨hifU⟩ := GorbowTheoryProofProof.monotonicity T U hTU (ctx+1) _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hif⟩
 obtain ⟨hs'⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) (liftTerm fuel) _ _ _ (.base hifU) hs
 obtain ⟨hsg⟩ := AccumulatorInstallation.stepGraph p installed lhs rhs t old a baseX base step B G R A (.var 0) liftedInputs
 obtain ⟨hsgU⟩ := GorbowTheoryProofProof.monotonicity T U hTU (ctx+1) _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hsg⟩
 obtain ⟨hs''⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U [] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) (liftTerm fuel) _ _ _ (.base hsgU) hs'
 have hsFinal := Hilbert.Local.finish hs''
 have hsInput : Nonempty (Derivation U
  (core I.currentK.coreTag (liftTerm (Term.numeral (n := ctx) (Encodable.encode c))) (liftTerm fuel)
   (impValue J.ctag J.atag
    (CurrentRecursionAccumulator.familyCall A.formulaTag (.var 0) ((Term.numeral R.qTag ::ᵥ inputs).map liftTerm))
    (CurrentRecursionAccumulator.familyCall A.formulaTag (.succ (.var 0)) ((Term.numeral R.qTag ::ᵥ inputs).map liftTerm)))
   (CurrentRecursionAccumulator.familyCall A.stepTag (.var 0) ((Term.numeral R.qTag ::ᵥ inputs).map liftTerm)))) := by
  simp only [List.Vector.map_cons,liftTerm,renameTerm,Logic.substNumeral,liftedInputs,impValue] at hsFinal ⊢
  exact ⟨hsFinal⟩
 obtain ⟨hacc⟩ := CurrentRecursionAccumulator.StatementChecks.exactAccumulator installed lhs rhs k t old a baseX pF pR I
  (m+1) (CurrentRecursionBaseProgram.program base B) (CurrentRecursionProducerProgram.formula base step)
  (CurrentRecursionProducerProgram.step base step G) A ctx (Term.numeral R.qTag ::ᵥ inputs)
  (Term.numeral (Encodable.encode c)) fuel counter ⟨hbFinal⟩ hsInput
 have hc := Derivation.mp (.logical (.andLeft _ _)) hacc
 obtain ⟨hff⟩ := AccumulatorInstallation.formulaGraph p installed lhs rhs t old a baseX base step B G R A counter inputs
 obtain ⟨hffU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨hff⟩
 obtain ⟨hcf⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hffU) (.base hc)
 obtain ⟨hpublic⟩ := AccumulatorInstallation.publicGraph p installed lhs rhs t old a baseX base step B G R A counter inputs
 obtain ⟨hpublicU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hpublic⟩
 obtain ⟨hcc⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U [] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hpublicU) hcf
 obtain ⟨ha⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p installed lhs rhs t old a _ I U hTU []
  _ _ (Term.numeral (Encodable.encode c)) fuel hcc
 exact ⟨Hilbert.Local.finish ha⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorProof
