module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EntriesLogic

def claim {ctx : Nat} q ctag (value rest index : Term ctx) : Formula ctx :=
 .imp (entries q value rest) (entry q value (HistoryLookup.consCall ctag value rest) index)
theorem substClaim {m n : Nat} (s : Fin m → Term n) q ctag (value rest index : Term m) :
 substituteFormula s (claim q ctag value rest index) =
 claim q ctag (substitute s value) (substitute s rest) (substitute s index) := by
 simp only [claim,substituteFormula,substEntries,substEntry,HistoryLookup.DropEquationsProof.substCons]

theorem zero {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim q ctag value rest .zero)) := by
 obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc ctx value rest
 have h : Derivation (GorbowPRNumeralCalculation.Theory p)
  (entry q value (HistoryLookup.consCall ctag value rest) .zero) := .mp (.logical (.orRight _ _)) hz
 exact ⟨Hilbert.lift _ h⟩

theorem next {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value rest index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim q ctag value rest (.succ index))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := entries q value rest
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hi := Hilbert.Local.mp (.base (eliminate q value rest index)) hh
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc ctx index value rest
 have hout := Hilbert.Local.mp (.mp (.base (optionTransport value (HistoryLookup.lookupCall q index rest)
  (HistoryLookup.lookupCall q (.succ index) (HistoryLookup.consCall ctag value rest))))
  (.base (Support.equalitySymmetry _ _ hs))) hi
 exact ⟨hout.discharge.finish⟩

theorem atIndex {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value rest index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim q ctag value rest index)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := claim q ctag (liftTerm value) (liftTerm rest) (.var (0 : Fin (ctx+1)))
 obtain ⟨hz⟩ := zero p q ctag hq hc value rest
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substClaim,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p q ctag hq hc (liftTerm value) (liftTerm rest) (.var (0 : Fin (ctx+1)))
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simp only [phi,GorbowStandardInduction.successorInstance,substClaim,substitute,successorLift,Fin.cases_zero]
  exact Hilbert.lift _ hn
 have h := atTerm phi index (HistoryCodec.ArithmeticSupport.induction phi hb hs)
 simpa only [phi,GorbowStandardInstances.instantiate,substClaim,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using (show Nonempty _ from ⟨h⟩)

theorem cons {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q value rest) (entries q value (HistoryLookup.consCall ctag value rest)))) := by
 let H := entries q value rest
 obtain ⟨h⟩ := atIndex p q ctag hq hc (liftTerm value) (liftTerm rest) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken H)
   (entry q (liftTerm value) (liftTerm (HistoryLookup.consCall ctag value rest)) (.var 0))) := by
  simpa only [H,claim,GorbowPACore.weaken,substEntries,liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder H _ h'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesConsProof
