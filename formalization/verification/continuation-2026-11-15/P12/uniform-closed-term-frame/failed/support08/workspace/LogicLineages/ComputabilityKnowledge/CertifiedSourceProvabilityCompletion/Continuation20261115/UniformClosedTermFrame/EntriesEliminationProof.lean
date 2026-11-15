module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesLogic
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesEliminationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EntriesLogic

theorem head {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value first rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q value (HistoryLookup.consCall ctag first rest)) (.equal first value))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := entries q value (HistoryLookup.consCall ctag first rest)
 let Z := Formula.equal (.succ first) .zero
 let S := Formula.equal (.succ first) (.succ value)
 let Q := Formula.equal first value
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hi := Hilbert.Local.mp (.base (eliminate q value (HistoryLookup.consCall ctag first rest) .zero)) hh
 obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p q ctag hq hc ctx first rest
 have hd := Hilbert.Local.mp (.mp (.base (optionTransport value _ (.succ first))) (.base hz)) hi
 have hbad : Hilbert.Local T ctx [Z] Z := .hypothesis List.mem_cons_self
 have hzero := Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero first)))
 have hs : Hilbert.Local T ctx [S] S := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.arithmetic (.succInjective first value))) hs
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z S Q)))
  (.base hzero.discharge.finish)) (.base he.discharge.finish)) hd
 exact ⟨hout.discharge.finish⟩

theorem tailAt {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value first rest index : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q value (HistoryLookup.consCall ctag first rest)) (entry q value rest index))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := entries q value (HistoryLookup.consCall ctag first rest)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hi := Hilbert.Local.mp (.base (eliminate q value (HistoryLookup.consCall ctag first rest) (.succ index))) hh
 obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p q ctag hq hc ctx index first rest
 have hout := Hilbert.Local.mp (.mp (.base (optionTransport value _ (HistoryLookup.lookupCall q index rest))) (.base hs)) hi
 exact ⟨hout.discharge.finish⟩

theorem tail {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value first rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q value (HistoryLookup.consCall ctag first rest)) (entries q value rest))) := by
 let H := entries q value (HistoryLookup.consCall ctag first rest)
 obtain ⟨h⟩ := tailAt p q ctag hq hc (liftTerm value) (liftTerm first) (liftTerm rest) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken H) (entry q (liftTerm value) (liftTerm rest) (.var 0))) := by
  simpa only [H,GorbowPACore.weaken,substEntries,liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder H _ h'⟩

theorem nil {n ctx : Nat} (p : Program n) (q : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩) (value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (entries q value .zero)) := by
 obtain ⟨hn⟩ := HistoryLookup.LookupProof.internalLookupNil n p q hq (ctx+1) (.var 0)
 have h : Derivation (GorbowPRNumeralCalculation.Theory p)
  (entry q (liftTerm value) .zero (.var 0)) := .mp (.logical (.orLeft _ _)) hn
 exact ⟨.generalize h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesEliminationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesEliminationProof
