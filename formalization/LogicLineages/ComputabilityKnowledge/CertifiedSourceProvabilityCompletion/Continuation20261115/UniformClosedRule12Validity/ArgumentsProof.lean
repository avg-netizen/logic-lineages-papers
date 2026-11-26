module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ArgumentsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Actual two-cons length, computed internally for arbitrary raw terms. -/
theorem lengthThree {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t u : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLengthOffset.lengthCall I.len (UniformClosedRule12.argumentsValue I.ctag f t u)) (Term.numeral 3))) := by
 obtain ⟨hz⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p I.len I.h_len ctx
 obtain ⟨hu⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p I.len I.ctag I.h_len I.h_ctag ctx u .zero
 obtain ⟨ht⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p I.len I.ctag I.h_len I.h_ctag ctx t (HistoryLookup.consCall I.ctag u .zero)
 obtain ⟨hf⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p I.len I.ctag I.h_len I.h_ctag ctx f (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))
 have hz' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (HistoryLengthOffset.lengthCall I.len (.zero : Term ctx)) .zero) := .base hz
 have hu' := localTrans _ _ _ (.base hu) (localUnary (.succ (.var 0)) _ _ hz')
 have htail := localTrans _ _ _ (.base ht) (localUnary (.succ (.var 0)) _ _ hu')
 have hout := localTrans _ _ _ (.base hf) (localUnary (.succ (.var 0)) _ _ htail)
 exact ⟨hout.finish⟩
/-- Both original decoders, preserving literal list order. -/
theorem first {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t u : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedCase12.firstValue I.htag (UniformClosedRule12.argumentsValue I.ctag f t u)) f)) :=
 HistoryLookup.DestructorProof.internalHeadCons n p I.htag I.ctag I.h_htag I.h_ctag ctx f (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))
theorem second {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t u : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedCase12.secondValue I.htag I.ttag (UniformClosedRule12.argumentsValue I.ctag f t u)) t)) := by
 obtain ⟨ht⟩ := HistoryLookup.DestructorProof.internalTailCons n p I.ttag I.ctag I.h_ttag I.h_ctag ctx f (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))
 obtain ⟨hh⟩ := HistoryLookup.DestructorProof.internalHeadCons n p I.htag I.ctag I.h_htag I.h_ctag ctx t (HistoryLookup.consCall I.ctag u .zero)
 have hc := HistoryLookup.DestructorProof.unaryCallCongruence I.htag _ _ ht
 exact ⟨Logic.trans _ _ _ hc hh⟩
theorem third {n ctx : Nat} (p : Program n) (I : GraphInstallation p) (f t u : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedCase12.thirdValue I.htag I.ttag (UniformClosedRule12.argumentsValue I.ctag f t u)) u)) := by
 obtain ⟨h1⟩ := HistoryLookup.DestructorProof.internalTailCons n p I.ttag I.ctag I.h_ttag I.h_ctag ctx f
  (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))
 obtain ⟨h2⟩ := HistoryLookup.DestructorProof.internalTailCons n p I.ttag I.ctag I.h_ttag I.h_ctag ctx t
  (HistoryLookup.consCall I.ctag u .zero)
 obtain ⟨h3⟩ := HistoryLookup.DestructorProof.internalHeadCons n p I.htag I.ctag I.h_htag I.h_ctag ctx u .zero
 have htail := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.ttag _ _ h1) h2
 exact ⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.htag _ _ htail) h3⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ArgumentsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ArgumentsProof
