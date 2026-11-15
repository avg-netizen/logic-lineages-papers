module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.BranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
/-- Total internal graph: all guards remain in the conclusion; both rejection
possibilities are eliminated inside the original Hilbert calculus. -/
theorem internalGuardedGraph : Targets.InternalGuardedGraph := by
 intro n p itag ftag fval vtag ptag ctag rtag hi hf hfv hv hp hc hr ctx formula replacement
 let T := GorbowPRNumeralCalculation.Theory p
 let F := Formula.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero)
 let V := Continuation20261114.RawReflexivityDispatcher.valid vtag replacement
 let A := guards fval vtag formula replacement
 let Q := Formula.equal (instanceCall itag formula replacement) (.zero : GorbowSyntax.Term ctx)
 have hy : Derivation T (.imp A (.equal (instanceCall itag formula replacement)
  (.succ (outputValue ftag ptag ctag rtag formula replacement)))) := by
  have hh : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
  have hF := Hilbert.Local.mp (.base (.logical (.andLeft F V))) hh
  have hV := Hilbert.Local.mp (.base (.logical (.andRight F V))) hh
  obtain ⟨hout⟩ := BranchProof.accepted p [A] ftag fval vtag ptag ctag rtag hf hfv hv hp hc hr formula replacement hF hV itag hi
  exact hout.discharge.finish
 have hn : Derivation T (.imp (.neg A) Q) := by
  let G := [Formula.neg A]
  have hyes : Hilbert.Local T ctx (F :: G) Q := by
   have hvyes : Hilbert.Local T ctx (V :: F :: G) Q := by
    have hF : Hilbert.Local T ctx (V :: F :: G) F := .hypothesis (by simp [G])
    have hV : Hilbert.Local T ctx (V :: F :: G) V := .hypothesis List.mem_cons_self
    have hA := Hilbert.Local.mp (.mp (.base (.logical (.andIntro F V))) hF) hV
    have hnot : Hilbert.Local T ctx (V :: F :: G) (.neg A) := .hypothesis (by simp [G])
    exact Hilbert.Local.explosion Q hA hnot
   have hvno : Hilbert.Local T ctx (.neg V :: F :: G) Q := by
    have hF : Hilbert.Local T ctx (.neg V :: F :: G) F := .hypothesis (by simp [G])
    have hV : Hilbert.Local T ctx (.neg V :: F :: G) (.neg V) := .hypothesis List.mem_cons_self
    obtain ⟨hout⟩ := BranchProof.rejectTerm p (.neg V :: F :: G) fval vtag hfv hv formula replacement hF hV itag hi
    exact hout
   exact cases V Q hvyes hvno
  have hno : Hilbert.Local T ctx (.neg F :: G) Q := by
   have hF : Hilbert.Local T ctx (.neg F :: G) (.neg F) := .hypothesis List.mem_cons_self
   obtain ⟨hout⟩ := BranchProof.rejectFormula p (.neg F :: G) fval hfv formula replacement hF itag hi
   exact hout
  exact (cases F Q hyes hno).discharge.finish
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hy) hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.GraphProof
