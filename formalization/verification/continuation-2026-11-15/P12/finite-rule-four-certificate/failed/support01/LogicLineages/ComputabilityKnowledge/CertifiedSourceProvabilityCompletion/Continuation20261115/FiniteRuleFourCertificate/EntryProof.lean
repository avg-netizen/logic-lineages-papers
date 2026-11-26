module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel.EntryProof
/-- Two actual pair equations reconstruct the unchanged literal line number. -/
theorem lineExpanded {n ctx : Nat} (p : Program n) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (sigma : Sentence) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (Term.numeral (n := ctx) (FiniteRuleFourLeaf.lineCode sigma))
   (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag
    (Term.numeral (rawCode sigma)) (Term.numeral (EncodingProof.tailCode sigma)))))) := by
 obtain ⟨hi⟩ := EncodingProof.pair (ctx := ctx) p ptag hp (rawCode sigma) (EncodingProof.tailCode sigma)
 obtain ⟨ho⟩ := EncodingProof.pair (ctx := ctx) p ptag hp 0
  (Nat.pair (rawCode sigma) (EncodingProof.tailCode sigma))
 have hc := HistoryIteratorSuffix.StepSuffixProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) ptag .zero _ .zero _
  (.base (.logical (.reflexive .zero))) (.base hi)
 have he := (localTrans _ _ _ hc (.base ho)).finish
 rw [← EncodingProof.lineNumber sigma] at he
 exact ⟨Support.equalitySymmetry _ _ he⟩
/-- Actual entry decoding/new-history equation for the literal canonical line. -/
theorem newHistory {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (sigma : Sentence) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryKernel.EntryProof.newHistory tag (.zero : Term ctx)
   (Term.numeral (FiniteRuleFourLeaf.lineCode sigma)))
   (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag .zero
    (Term.numeral (rawCode sigma))) .zero))) := by
 obtain ⟨hl⟩ := lineExpanded (ctx := ctx) p ptag hp sigma
 have he := Logic.unary (HistoryKernel.EntryProof.newHistory tag .zero (.var (0 : Fin (ctx+1)))) _ _ hl
 simp only [HistoryKernel.EntryProof.newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at he
 obtain ⟨hv⟩ := TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact
  p tag ptag ctag ht hp hc .zero .zero (Term.numeral (rawCode sigma))
  (Term.numeral (EncodingProof.tailCode sigma))
 exact ⟨Logic.trans _ _ _ he hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EntryProof
