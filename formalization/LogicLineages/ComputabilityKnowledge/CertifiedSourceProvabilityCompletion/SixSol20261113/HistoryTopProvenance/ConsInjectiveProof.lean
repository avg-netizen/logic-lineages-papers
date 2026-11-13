module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsInjectiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem consInjective {n ctx : Nat} (p : Program n) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (a b c d : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryLookup.consCall ctag a b) (HistoryLookup.consCall ctag c d))
     (.conj (.equal a c) (.equal b d)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let pt := ctag + argumentTag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hp := Equations.argumentChild p ctag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 obtain ⟨ha⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a b
 obtain ⟨hb⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx c d
 obtain ⟨hi⟩ := HistoryCancellation.InjectivityProof.pairInjective n p pt hp ctx a b c d
 let E := Formula.equal (HistoryLookup.consCall ctag a b) (HistoryLookup.consCall ctag c d)
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hs := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base ha))
   (localTrans _ _ _ he (.base hb))
 have hpairs := Hilbert.Local.mp (.base (.arithmetic (.succInjective
   (HistoryKernel.pairCall pt a b) (HistoryKernel.pairCall pt c d)))) hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hi) hpairs))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsInjectiveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsInjectiveProof
