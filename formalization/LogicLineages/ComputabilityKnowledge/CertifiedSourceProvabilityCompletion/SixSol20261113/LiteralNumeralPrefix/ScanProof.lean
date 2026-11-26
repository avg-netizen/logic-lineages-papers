module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.InductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.EquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.TermScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InductionProof
section
variable {n ctx : Nat} (p : Program n) (ntag stag ptag ctag : Nat)
variable (hn : (nodes p)[ntag]? = some ⟨1,numeralCode⟩)
variable (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
include hn hs hp hc

theorem base (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ntag stag ptag ctag .zero binder rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let tasks := HistoryLookup.consCall ctag (termTask ptag binder) rest
 obtain ⟨hz⟩ := EquationsProof.zero p ntag ctag hn hc (ctx := ctx)
 have he := HistoryAppend.PositiveProof.binaryCongruence (T := T) stag tasks tasks _ _
  (.logical (.reflexive tasks)) hz
 obtain ⟨hscan⟩ := TermScanProof.scanZero p stag ptag ctag hs hp hc binder rest
 exact ⟨Logic.trans _ _ _ he hscan⟩

theorem step (value binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property ntag stag ptag ctag value binder rest)
   (property ntag stag ptag ctag (.succ value) binder rest))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let tasks := HistoryLookup.consCall ctag (termTask ptag binder) rest
 let H := property ntag stag ptag ctag value binder rest
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hnxt⟩ := EquationsProof.successor p ntag ctag hn hc value
 have he := HistoryAppend.PositiveProof.binaryCongruence (T := T) stag tasks tasks _ _
  (.logical (.reflexive tasks)) hnxt
 obtain ⟨hscan⟩ := TermScanProof.scanSucc p stag ptag ctag hs hp hc binder rest (numeralCall ntag value)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base he) (localTrans _ _ _ (.base hscan) hh)))⟩
end

theorem internalScan : Targets.InternalScan := by
 intro n p ntag stag ptag ctag hn hs hp hc ctx value binder rest
 obtain ⟨hz⟩ := base p ntag stag ptag ctag hn hs hp hc binder rest
 obtain ⟨hnxt⟩ := step p ntag stag ptag ctag hn hs hp hc (.var 0 : Term (ctx+1)) (liftTerm binder) (liftTerm rest)
 exact fromBaseStep ntag stag ptag ctag value binder rest hz hnxt
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ScanProof
