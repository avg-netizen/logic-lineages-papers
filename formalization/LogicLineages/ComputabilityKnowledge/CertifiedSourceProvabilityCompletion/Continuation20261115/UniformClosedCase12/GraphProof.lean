module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.BranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.GraphProof
open GorbowSyntax GorbowTheoryProof SixSol20261113
theorem internalCaseGraph : Targets.InternalCaseGraph := by
 intro n p qtag itag ltag htag ttag ctag atag hq hi hl hh ht hc ha ctx args left right
 let T := GorbowPRNumeralCalculation.Theory p
 let L := Formula.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)
 let A := Formula.equal (leftValue itag htag ttag args) (.succ left)
 let B := Formula.equal (rightValue itag htag ttag args) (.succ right)
 let Z := Formula.equal (leftValue itag htag ttag args) (.zero : Term ctx)
 let W := Formula.equal (rightValue itag htag ttag args) (.zero : Term ctx)
 have hL : Hilbert.Local T ctx [B,A,L] L := .hypothesis (by simp)
 have hA : Hilbert.Local T ctx [B,A,L] A := .hypothesis (by simp)
 have hB : Hilbert.Local T ctx [B,A,L] B := .hypothesis List.mem_cons_self
 obtain ⟨hy⟩ := BranchProof.accepted p [B,A,L] itag ltag htag ttag ctag atag
  hi hl hh ht hc ha args left right hL hA hB qtag hq
 have hnotL : Hilbert.Local T ctx [.neg L] (.neg L) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := BranchProof.rejectLength p [.neg L] ltag hl args hnotL qtag hq
 have hZ : Hilbert.Local T ctx [Z] Z := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := BranchProof.rejectLeft p [Z] itag htag ttag hi hh ht args hZ qtag hq
 have hW : Hilbert.Local T ctx [W] W := .hypothesis List.mem_cons_self
 obtain ⟨hw⟩ := BranchProof.rejectRight p [W] itag htag ttag hi hh ht args hW qtag hq
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hy.discharge.discharge.discharge.finish)
  (.mp (.mp (.logical (.andIntro _ _)) hn.discharge.finish)
   (.mp (.mp (.logical (.andIntro _ _)) hz.discharge.finish) hw.discharge.finish))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.GraphProof
