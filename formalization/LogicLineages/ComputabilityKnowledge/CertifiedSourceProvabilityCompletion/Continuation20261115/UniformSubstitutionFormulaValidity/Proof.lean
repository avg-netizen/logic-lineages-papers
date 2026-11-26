module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.ResultProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.Proof
open GorbowSyntax GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The actual formula validator is preserved by the actual raw-fold output,
with symbolic binder depth and arbitrary runtime formula/replacement terms. -/
theorem formulaOutputValidity : Targets.InternalFormulaOutputValidity := by
 intro n p ftag etag vtag fval stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr hfv ctx depth tokens replacement
 obtain ⟨fs,fp,fc,eqtag,_,_,_,heq⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p fval hfv
 let oldTasks := LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag (.succ depth)
 let newTasks := LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag depth
 let out := substitutedOutput ftag ptag ctag r depth tokens replacement
 obtain ⟨hrel⟩ := RelationProof.singleton p len q l r ptag ctag hlen hq hl hr hp hc depth
 obtain ⟨hfold⟩ := UniformSubstitutionFoldTransport.StatementChecks.exactFoldTransport n p
  ftag etag vtag stepTag stag ptag ctag atag dtag len q l r
  hf he hv hstep hs hp hc ha hd hlen hq hl hr ctx tokens oldTasks newTasks .zero replacement
 obtain ⟨hsound⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p fval stag ptag ctag eqtag
  hfv hs hp hc heq (.succ depth) tokens
 obtain ⟨hresult⟩ := ResultProof.complete p stag len q l r ctag hlen hc newTasks out
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p fval stag ptag ctag eqtag
  hfv hs hp hc heq depth out
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag replacement
 let F := Formula.equal (LiteralSyntaxValidator.formulaCall fval (.succ depth) tokens) (.succ .zero)
 let G := [F,V]
 have hvv : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hff : Hilbert.Local T ctx G F := .hypothesis (by simp [G])
 have hold := Hilbert.Local.mp (.base hsound) hff
 have hw := Hilbert.Local.mp (.mp (.mp (.base hfold) hvv) (.base hrel)) hold
 have hscan := Hilbert.Local.mp (.base hresult) hw
 have hout := Hilbert.Local.mp (.base hcomplete) hscan
 exact ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.Proof
