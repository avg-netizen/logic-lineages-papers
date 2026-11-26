module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.EntryProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel.EntryProof

theorem rawNewHistory {n ctx : Nat} (p : Program n) (f : Formula 1) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p f old arithmetic x) (raw : Term ctx)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (call I.qtag (raw ::ᵥ nil)))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero
    (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)) .zero))) := by
 obtain ⟨hq⟩ := FullFormulaInstantiation.StatementChecks.exactInternalLine f n p I.qtag I.ptag I.ctag I.atag
  I.hq I.hp I.hc I.ha ctx raw
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.ptag I.ctag
  ht I.hp I.hc .zero .zero (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)
  (HistoryKernel.pairCall I.ptag .zero
   (HistoryKernel.pairCall I.ptag (Term.numeral 13)
    (HistoryKernel.pairCall I.ptag (HistoryLookup.consCall I.ctag (Term.numeral (FullFormulaInstantiation.templateCode a b))
     (HistoryLookup.consCall I.ctag raw .zero))
     (HistoryKernel.pairCall I.ptag .zero .zero))))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.EntryProof
