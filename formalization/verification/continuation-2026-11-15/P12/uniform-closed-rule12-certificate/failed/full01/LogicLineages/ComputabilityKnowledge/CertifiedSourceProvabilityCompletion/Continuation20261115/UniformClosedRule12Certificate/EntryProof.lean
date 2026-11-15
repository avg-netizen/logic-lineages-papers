module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.EntryProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel.EntryProof
/-- Exact original kernel entry update for the runtime three-argument line. -/
theorem rawNewHistory {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (formula leftTerm rightTerm : Term ctx)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (UniformClosedRule12.lineCall I.constructorTag formula leftTerm rightTerm))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero
    (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)) .zero))) := by
 obtain ⟨hq⟩ := UniformClosedRule12.StatementChecks.exactInternalLine n p I.constructorTag I.caseTag I.predTag I.ptag I.ctag
  I.h_constructor I.h_caseTag I.h_predTag I.h_ptag I.h_ctag ctx formula leftTerm rightTerm
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.ptag I.ctag
  ht I.h_ptag I.h_ctag .zero .zero (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)
  (HistoryKernel.pairCall I.ptag .zero
   (HistoryKernel.pairCall I.ptag (Term.numeral 12)
    (HistoryKernel.pairCall I.ptag (UniformClosedRule12.argumentsValue I.ctag formula leftTerm rightTerm)
     (HistoryKernel.pairCall I.ptag .zero .zero))))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.EntryProof
