module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.EquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.InductionSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.AccumulatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem exactAccumulator : Targets.InternalAccumulator := by
 intro installed lhs rhs k t old a baseX pF pR I m base formula step R ctx params index fuel counter
 dsimp only
 intro hbase hstep
 obtain ⟨hbase⟩ := hbase
 obtain ⟨hstep⟩ := hstep
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨hz⟩ := EquationsProof.zero p base formula step R params
 obtain ⟨hz⟩ := GorbowTheoryProofProof.monotonicity _ U hTU ctx _ ⟨hz⟩
 obtain ⟨hzero⟩ := RebaseProof.coreCode U [] I.currentK.coreTag index fuel (familyCall R.formulaTag .zero params)
  (call R.baseTag params) (familyCall R.producerTag .zero params)
  (.base (.mp (Logic.symmetryRule U _ _) hz)) (.base hbase)
 let params' := params.map liftTerm
 let index' := liftTerm index
 let fuel' := liftTerm fuel
 let prior := InductionSupport.property I.currentK.coreTag R.formulaTag R.producerTag
  (.var 0 : Term (ctx+1)) index' fuel' params'
 have hi : Hilbert.Local U (ctx+1) [prior] prior := .hypothesis (List.mem_cons_self)
 obtain ⟨hmp⟩ := AlgebraSupport.one p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)
  I U hTU [prior] (familyCall R.formulaTag (.var 0) params') (familyCall R.formulaTag (.succ (.var 0)) params')
  (familyCall R.stepTag (.var 0) params') (familyCall R.producerTag (.var 0) params') index' fuel'
  (.base hstep) hi
 obtain ⟨hs⟩ := EquationsProof.successor p base formula step R
  I.previous.previous.previous.previous.previous.mpTag I.previous.previous.previous.previous.previous.hmp
  (.var 0 : Term (ctx+1)) params'
 obtain ⟨hs⟩ := GorbowTheoryProofProof.monotonicity _ U hTU (ctx+1) _ ⟨hs⟩
 obtain ⟨hnext⟩ := RebaseProof.coreCode U [prior] I.currentK.coreTag index' fuel'
  (familyCall R.formulaTag (.succ (.var 0)) params') _
  (familyCall R.producerTag (.succ (.var 0)) params') (.base (.mp (Logic.symmetryRule U _ _) hs)) hmp
 have hsuccessor := Hilbert.Local.finish (Hilbert.Local.discharge hnext)
 obtain ⟨hcore⟩ := InductionSupport.fromBaseStep I.currentK.coreTag R.formulaTag R.producerTag
  counter index fuel params (Hilbert.Local.finish hzero) hsuccessor
 obtain ⟨ha⟩ := AlgebraSupport.acceptedOfCore p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)
  I U hTU [] (familyCall R.formulaTag counter params) (familyCall R.producerTag counter params)
  index fuel (.base hcore)
 exact ⟨Hilbert.Local.finish ha⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.AccumulatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.AccumulatorProof
