module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.StateLinesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.State.PairedProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalStateRetention RawUniversalStateRetention.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix HistoryIteratorSuffix.WitnessProof HistoryIteratorSuffix.StepSuffixProof
open RawUniversalStateRetention.TransportProof

theorem internalPairedStep : Targets.InternalPairedStep := by
 intro n p v l a x ot nt ptag ctag ho hn hp hc ctx option lines index fuel out rest
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := preserves ot nt ptag (pairCall ptag option lines) index fuel out rest
 let E := Formula.equal option .zero
 obtain ⟨hno⟩ := NoneProof.noneReject p ot ptag ctag v l a x ho hp hc index fuel out rest lines
 let A := Formula.equal (kernelCall ot (pairCall ptag .zero lines) index fuel) (pairCall ptag (.succ out) rest)
 let B := Formula.equal (kernelCall nt (pairCall ptag .zero lines) index fuel) (pairCall ptag (.succ out) rest)
 have bad : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hz : Derivation T (preserves ot nt ptag (pairCall ptag .zero lines) index fuel out rest) :=
  Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.explosion B bad (.base hno)))
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have stateEq := pairCongruence ptag .zero lines option lines
  (HistoryOrder.StepProof.localSym _ _ he) (.base (.logical (.reflexive _)))
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (moveState ot nt ptag _ _ index fuel out rest)) stateEq) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody option
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm option) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := LinesProof.generalStep p ot nt ptag ctag v l a x ho hn hp hc
  (liftTerm index) (liftTerm fuel) (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm rest) (liftTerm lines)
 have ep := pairCongruence ptag (.succ (.var 0)) (liftTerm lines) (liftTerm option) (liftTerm lines)
  (HistoryOrder.StepProof.localSym _ _ hh) (.base (.logical (.reflexive _)))
 have hout : Hilbert.Local T (ctx+1) [H] (GorbowPACore.weaken Q) := by
  simp only [Q,weakenPreserves,liftTerm,renameTerm,substPair,substitute]
  exact .mp (.mp (.base (moveState ot nt ptag _ _ _ _ _ _)) ep) (.base hs)
 obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T option
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hcases⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.State.PairedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.State.PairedProof
