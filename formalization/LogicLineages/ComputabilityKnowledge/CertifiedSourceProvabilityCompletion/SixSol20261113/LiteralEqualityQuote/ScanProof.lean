module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.TermScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix LiteralRawMP.ConstructorSupportProof

private theorem selfComputes {n k ctx : Nat} (p : Program n) (q : Program k)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨k,q⟩) (args : List.Vector (Term ctx) k) :
 Computes p q args (call tag args) := by
 intro other ho
 exact GorbowPRInternalCoherence.Proof.registryCoherence n p other tag k q ho ht ctx args

theorem internalScan : Targets.InternalScan := by
 intro k t u n p tag stag ptag ctag atag ht hs hp hc ha ctx args binder rest
 let q := LiteralTemplateQuote.templateQuote t
 let r := LiteralTemplateQuote.templateQuote u
 let g : Fin 2 → Program k := Fin.cases (constant k 0) (Fin.cases (applyTwo HistoryAppend.append q r) Fin.elim0)
 let inner := tag + argumentTag HistoryCodec.cons g 1
 have hi : (nodes p)[inner]? = some ⟨k,applyTwo HistoryAppend.append q r⟩ :=
  Equations.argumentChild p tag HistoryCodec.cons g ht 1
 let gi : Fin 2 → Program k := Fin.cases q (Fin.cases r Fin.elim0)
 let qt := inner + argumentTag HistoryAppend.append gi 0
 let rt := inner + argumentTag HistoryAppend.append gi 1
 have hq : (nodes p)[qt]? = some ⟨k,q⟩ := Equations.argumentChild p inner HistoryAppend.append gi hi 0
 have hr : (nodes p)[rt]? = some ⟨k,r⟩ := Equations.argumentChild p inner HistoryAppend.append gi hi 1
 have happ := binary p args HistoryAppend.append atag ha q r (call qt args) (call rt args)
  (selfComputes p q qt hq args) (selfComputes p r rt hr args)
 obtain ⟨he⟩ := binary p args HistoryCodec.cons ctag hc (constant k 0)
  (applyTwo HistoryAppend.append q r) (Term.numeral 0)
  (HistoryAppend.appendCall atag (call qt args) (call rt args)) (constantValue p args 0) happ tag ht
 let formula := HistoryLookup.consCall ctag (formulaTask ptag binder) rest
 let one := HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag binder) rest
 let two := HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag binder) one
 have heq := HistoryAppend.PositiveProof.binaryCongruence (T := GorbowPRNumeralCalculation.Theory p)
  stag formula formula _ _ (.logical (.reflexive _)) he
 obtain ⟨h1⟩ := TermScanProof.scanEquality p stag ptag ctag hs hp hc binder rest
  (HistoryAppend.appendCall atag (call qt args) (call rt args))
 obtain ⟨hleft⟩ := LiteralTemplateQuote.ScanProof.internalScan k t n p qt stag ptag ctag atag
  hq hs hp hc ha ctx args binder one
 obtain ⟨hf⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx
  two (call qt args) (call rt args) one
 obtain ⟨hright⟩ := LiteralTemplateQuote.ScanProof.internalScan k u n p rt stag ptag ctag atag
  hr hs hp hc ha ctx args binder rest
 exact ⟨Logic.trans _ _ _ heq (Logic.trans _ _ _ h1 (Logic.trans _ _ _ (.mp hf hleft) hright))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ScanProof
