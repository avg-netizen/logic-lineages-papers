module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel.EntryProof

theorem rawNewHistory {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (raw rawB rawV : Term ctx)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (RawAddLeftReplace.lineCall I.qtag raw rawB rawV))
   (HistoryLookup.consCall I.consTag (HistoryKernel.pairCall I.pairTag .zero
    (RawAddLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV)) .zero))) := by
 obtain ⟨hq⟩ := RawAddLeftReplace.StatementChecks.exactInternalLine n p I.qtag I.pairTag I.consTag I.appendTag
  I.hq I.hp I.hc I.ha ctx raw rawB rawV
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.pairTag I.consTag
  ht I.hp I.hc .zero .zero (RawAddLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV)
  (HistoryKernel.pairCall I.pairTag .zero
   (HistoryKernel.pairCall I.pairTag (Term.numeral 12)
    (HistoryKernel.pairCall I.pairTag (HistoryLookup.consCall I.consTag (RawAddLeftReplace.templateValue I.consTag I.appendTag raw rawV)
     (HistoryLookup.consCall I.consTag raw (HistoryLookup.consCall I.consTag rawB .zero)))
     (HistoryKernel.pairCall I.pairTag .zero .zero))))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.EntryProof
