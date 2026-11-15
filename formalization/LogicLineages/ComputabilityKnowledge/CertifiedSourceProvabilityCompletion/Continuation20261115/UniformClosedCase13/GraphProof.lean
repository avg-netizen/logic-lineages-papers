module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.BranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.GraphProof
open GorbowSyntax GorbowTheoryProof SixSol20261113
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
/-- Whole arbitrary encoded argument lists. The None branch internally splits
length equality, so it carries no hidden length or canonical-list premise. -/
theorem internalCaseGraph : Targets.InternalCaseGraph := by
 intro n p qtag itag ltag htag ttag ctag atag hq hi hl hh ht hc ha ctx args result
 let T := GorbowPRNumeralCalculation.Theory p
 let L := Formula.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)
 let I := Formula.equal (instanceValue itag htag ttag args) (.succ result)
 let Z := Formula.equal (instanceValue itag htag ttag args) (.zero : Term ctx)
 let Q := Formula.equal (caseCall qtag args) (.zero : Term ctx)
 have hL : Hilbert.Local T ctx [I,L] L := .hypothesis (by simp)
 have hI : Hilbert.Local T ctx [I,L] I := .hypothesis List.mem_cons_self
 obtain ⟨hy⟩ := BranchProof.accepted p [I,L] itag ltag htag ttag ctag atag hi hl hh ht hc ha args result hL hI qtag hq
 have hnotL : Hilbert.Local T ctx [.neg L] (.neg L) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := BranchProof.rejectLength p [.neg L] ltag hl args hnotL qtag hq
 have hLy : Hilbert.Local T ctx [L,Z] L := .hypothesis List.mem_cons_self
 have hZy : Hilbert.Local T ctx [L,Z] Z := .hypothesis (by simp)
 obtain ⟨hzy⟩ := BranchProof.rejectNone p [L,Z] itag ltag htag ttag hi hl hh ht args hLy hZy qtag hq
 have hLn : Hilbert.Local T ctx [.neg L,Z] (.neg L) := .hypothesis List.mem_cons_self
 obtain ⟨hzn⟩ := BranchProof.rejectLength p [.neg L,Z] ltag hl args hLn qtag hq
 have hz : Hilbert.Local T ctx [Z] Q := cases L Q hzy hzn
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hy.discharge.discharge.finish)
  (.mp (.mp (.logical (.andIntro _ _)) hn.discharge.finish) hz.discharge.finish)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.GraphProof
