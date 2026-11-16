module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInputs
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem quoteGraph {arity inputs n depth external ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (f : Formula n) (e : FixedFormulaSubstitution.Environment n depth external) (raw : Fin external → Program inputs)
 (values : List.Vector (Term ctx) external) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : ∀ i, Computes p (raw i) args (values.get i)) :
 Computes p (.composition (FixedFormulaSubstitution.formulaProgram f e) raw) args
  (FixedFormulaSubstitution.formulaValue ctag atag values f e) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag _ raw ht args values
  (fun i => hr i _ (Equations.argumentChild p tag _ raw ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalFormula n depth external e f arity p (tag+1) ctag atag
  (Equations.functionChild p tag _ raw ht) hc ha ctx values
 exact ⟨Logic.trans _ _ _ he hf⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateGraph
