module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.DispatcherProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.EntryProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel.EntryProof
/-- Exact original kernel entry update for the runtime three-argument line. -/
theorem rawNewHistory {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p f lhs rhs rawOld arithmetic x isS) (formula leftTerm : Term ctx)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (OriginalQuantifierLogicalProducers.lineCall I.quantifierTag formula leftTerm))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero
    (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)) .zero))) := by
 obtain ⟨⟨hq⟩,_⟩ := OriginalQuantifierLogicalProducers.StatementChecks.exactInternal n p isS
  I.ptag I.ctag I.atag I.quantifierTag I.singletonTag ⟨I.h_ptag,I.h_ctag,I.h_atag⟩
  I.h_quantifierTag I.h_singletonTag ctx formula leftTerm
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.ptag I.ctag
  ht I.h_ptag I.h_ctag .zero .zero (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)
  (HistoryKernel.pairCall I.ptag .zero
   (HistoryKernel.pairCall I.ptag (Term.numeral (if isS then 10 else 2))
    (HistoryKernel.pairCall I.ptag (OriginalQuantifierLogicalProducers.argumentsValue isS I.ctag formula leftTerm)
     (HistoryKernel.pairCall I.ptag .zero .zero))))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.EntryProof
