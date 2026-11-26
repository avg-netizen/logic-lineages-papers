module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryKernel.EntryProof

theorem rawNewHistory {n ctx : Nat} (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x) (raw rawB : Term ctx)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (RawAddSucc.lineCall I.qtag raw rawB))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero
    (RawAddSucc.equalityValue I.ctag I.atag raw rawB)) .zero))) := by
 obtain ⟨hq⟩ := RawAddSucc.StatementChecks.exactInternalLine n p I.qtag I.ptag I.ctag I.atag
  I.hq I.hp I.hc I.ha ctx raw rawB
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.ptag I.ctag
  ht I.hp I.hc .zero .zero (RawAddSucc.equalityValue I.ctag I.atag raw rawB)
  (HistoryKernel.pairCall I.ptag (.succ .zero)
   (HistoryKernel.pairCall I.ptag (Term.numeral 3)
    (HistoryKernel.pairCall I.ptag (HistoryLookup.consCall I.ctag raw (HistoryLookup.consCall I.ctag rawB .zero))
     (HistoryKernel.pairCall I.ptag .zero .zero))))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate.EntryProof
