module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ArgumentsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Actual two-cons length, computed internally for arbitrary raw terms. -/
theorem lengthTwo {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLengthOffset.lengthCall I.len (UniformClosedRule13.argumentsValue I.ctag f t)) (Term.numeral 2))) := by
 obtain ⟨hz⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p I.len I.h_len ctx
 obtain ⟨ht⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p I.len I.ctag I.h_len I.h_ctag ctx t .zero
 obtain ⟨hf⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p I.len I.ctag I.h_len I.h_ctag ctx f (HistoryLookup.consCall I.ctag t .zero)
 have hz' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (HistoryLengthOffset.lengthCall I.len (.zero : Term ctx)) .zero) := .base hz
 have htail := localTrans _ _ _ (.base ht) (localUnary (.succ (.var 0)) _ _ hz')
 have hout := localTrans _ _ _ (.base hf) (localUnary (.succ (.var 0)) _ _ htail)
 exact ⟨hout.finish⟩
/-- Both original decoders, preserving literal list order. -/
theorem first {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedCase13.firstValue I.htag (UniformClosedRule13.argumentsValue I.ctag f t)) f)) :=
 HistoryLookup.DestructorProof.internalHeadCons n p I.htag I.ctag I.h_htag I.h_ctag ctx f (HistoryLookup.consCall I.ctag t .zero)
theorem second {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedCase13.secondValue I.htag I.ttag (UniformClosedRule13.argumentsValue I.ctag f t)) t)) := by
 obtain ⟨ht⟩ := HistoryLookup.DestructorProof.internalTailCons n p I.ttag I.ctag I.h_ttag I.h_ctag ctx f (HistoryLookup.consCall I.ctag t .zero)
 obtain ⟨hh⟩ := HistoryLookup.DestructorProof.internalHeadCons n p I.htag I.ctag I.h_htag I.h_ctag ctx t .zero
 have hc := HistoryLookup.DestructorProof.unaryCallCongruence I.htag _ _ ht
 exact ⟨Logic.trans _ _ _ hc hh⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ArgumentsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ArgumentsProof
