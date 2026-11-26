module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.StatePairedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.State.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalStateRetention RawUniversalStateRetention.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix HistoryIteratorSuffix.WitnessProof HistoryIteratorSuffix.StepSuffixProof
open RawUniversalStateRetention.TransportProof

variable (testK testS : Program 1)

theorem internalStateStep : Targets.InternalStateStep testK testS := by
 intro n p v l a x ot nt ptag ctag ho hn hp hc ctx state index fuel out rest
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := preserves ot nt ptag state index fuel out rest
 let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm state)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) (liftTerm (liftTerm state))) := .hypothesis List.mem_cons_self
 obtain ⟨hpairs⟩ := PairedProof.internalPairedStep testK testS n p v l a x ot nt ptag ctag ho hn hp hc (ctx+2) A B
  (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)) (liftTerm (liftTerm out)) (liftTerm (liftTerm rest))
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base (moveState ot nt ptag _ _ _ _ _ _)) hh) (.base hpairs)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,weakenPreserves,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag state) Q ⟨hinner⟩
 obtain ⟨hs⟩ := SurjectivityProof.internalPairSurjective n p ptag hp ctx state
 exact ⟨.mp helim hs⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.State.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.State.Proof
