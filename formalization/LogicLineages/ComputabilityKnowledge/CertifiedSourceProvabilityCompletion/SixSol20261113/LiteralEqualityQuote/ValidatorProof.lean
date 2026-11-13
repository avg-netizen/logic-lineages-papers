module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof List.Vector
open SixSol20261112.Fuel HistoryRuleSuffix

theorem internalValidator : ValidatorTargets.InternalValidator := by
 intro k t u n p qtag vtag hq hv ctx values binder
 obtain ⟨stag,ptag,ctag,etag,hs,hp,hc,he⟩ :=
  LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p vtag hv
 let left := LiteralTemplateQuote.templateQuote t
 let right := LiteralTemplateQuote.templateQuote u
 let g : Fin 2 → Program k := Fin.cases (constant k 0)
  (Fin.cases (applyTwo HistoryAppend.append left right) Fin.elim0)
 let inner := qtag + argumentTag HistoryCodec.cons g 1
 have hi : (nodes p)[inner]? = some ⟨k,applyTwo HistoryAppend.append left right⟩ :=
  Equations.argumentChild p qtag HistoryCodec.cons g hq 1
 let gi : Fin 2 → Program k := Fin.cases left (Fin.cases right Fin.elim0)
 have ha : (nodes p)[inner+1]? = some ⟨2,HistoryAppend.append⟩ :=
  Equations.functionChild p inner HistoryAppend.append gi hi
 obtain ⟨hscan⟩ := ScanProof.internalScan k t u n p qtag stag ptag ctag (inner+1)
  hq hs hp hc ha ctx values binder .zero
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p vtag stag ptag ctag etag
  hv hs hp hc he binder (quoteCall qtag values)
 exact ⟨.mp hcomplete hscan⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorProof
