module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.StateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Simulation.BasicProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalSimulation RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open RawUniversalSimulation.RelationProof RawUniversalSimulation.SupportProof

variable (test : Program 1)

theorem someEvolves {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
 (hn : (nodes p)[nt]? = some ⟨3,kernel v (extend test l) a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (h lines new index fuel out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (evolves ot nt ptag (pairCall ptag (.succ h) lines) new index fuel out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let old := pairCall ptag (.succ h) lines
 let R := relation ptag old new
 let H := Formula.equal (kernelCall ot old index fuel) (pairCall ptag (.succ out) rest)
 have hr : Hilbert.Local T ctx [H,R] R := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
 have en : Hilbert.Local T ctx [H,R] (.equal new old) :=
  .mp (.mp (.base (instanceRule ptag old new h lines)) hr) (.base (.logical (.reflexive old)))
 obtain ⟨hs⟩ := State.Proof.internalStateStep test n p v l a x ot nt ptag ctag ho hn hp hc ctx old index fuel out rest
 have next := Hilbert.Local.mp (.base hs) hh
 have ek := kernelCongruence nt new old index fuel en
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ ek next)))⟩

theorem noneEvolves {n ctx : Nat} (p : Program n) (ot nt ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ho : (nodes p)[ot]? = some ⟨3,kernel v l a x⟩)
 (hn : (nodes p)[nt]? = some ⟨3,kernel v (extend test l) a x⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (lines new index fuel out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (evolves ot nt ptag (pairCall ptag .zero lines) new index fuel out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let old := pairCall ptag .zero lines
 let R := relation ptag old new
 let H := Formula.equal (kernelCall ot old index fuel) (pairCall ptag (.succ out) rest)
 let Q := Formula.equal (kernelCall nt new index fuel) (pairCall ptag (.succ out) rest)
 obtain ⟨hno⟩ := HistoryIteratorSuffix.NoneProof.noneReject p ot ptag ctag v l a x ho hp hc index fuel out rest lines
 have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
 have hout : Hilbert.Local T ctx [H,R] Q := Hilbert.Local.explosion Q hh (.base hno)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Simulation.BasicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Simulation.BasicProof
