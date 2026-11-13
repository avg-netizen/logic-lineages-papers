module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationOperationalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalImplicationConclusion : Targets.InternalImplicationConclusion := by
 intro n p vtag atag ctag hv ha hc ctx binder antecedent conclusion
 obtain ⟨scanTag,ptag,_,eqtag,hscan,hp,_,heq⟩ := FormulaBindingProof.nodesInstalled p vtag hv
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨stag,hs⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stag hs
 let T := GorbowPRNumeralCalculation.Theory p
 let A := Formula.equal (formulaCall vtag binder antecedent) (.succ .zero)
 let I := Formula.equal (formulaCall vtag binder (binaryRaw atag ctag 7 antecedent conclusion)) (.succ .zero)
 have hA : Hilbert.Local T ctx [I,A] A := .hypothesis (by simp)
 have hI : Hilbert.Local T ctx [I,A] I := .hypothesis List.mem_cons_self
 obtain ⟨hante⟩ := FormulaBindingProof.sound p vtag scanTag ptag ctag eqtag hv hscan hp hc heq binder antecedent
 obtain ⟨himpl⟩ := FormulaBindingProof.sound p vtag scanTag ptag ctag eqtag hv hscan hp hc heq binder (binaryRaw atag ctag 7 antecedent conclusion)
 obtain ⟨hconcl⟩ := ImplicationOperationalProof.scanConclusion p scanTag itag ltag ptag rtag ctag stag etag atag hscan hi hl hp hr hc hs he ha binder antecedent conclusion
 have hout := Hilbert.Local.mp (.mp (.base hconcl) (.mp (.base hante) hA)) (.mp (.base himpl) hI)
 obtain ⟨hcomplete⟩ := FormulaBindingProof.complete p vtag scanTag ptag ctag eqtag hv hscan hp hc heq binder conclusion
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hcomplete) hout)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationProof
