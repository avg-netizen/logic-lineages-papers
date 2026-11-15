module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.FallbackProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NonIndexProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.IndexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof InternalAtomsProof IndexProof
/-- All ten actual internal branches, with no native-calibration dependency. -/
theorem internalBranches : Targets.InternalBranches := by
 intro n p etag ptag ctag he hp hc ctx token raw k bound rest depth gap
 refine ⟨FallbackProof.none p etag ctag he hc token raw,
  FallbackProof.empty p etag ctag he hc token raw,
  NonIndexProof.marker p etag ptag ctag he hp hc bound rest raw,
  NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest token raw,
  NonIndexProof.otherKind p etag ptag ctag he hp hc k bound rest token raw,?_,?_,?_,?_,?_⟩
 · let T := GorbowPRNumeralCalculation.Theory p
   let H := Formula.equal (.add token (.succ gap)) depth
   let G := [H]
   have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
   have hd := successorDepth p G ptag ctag hp hc (Term.numeral 2) depth rest token raw
   have hi := belowCase p G ctag hc (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) token depth gap raw hd hh
   obtain ⟨h⟩ := enterIndex p G ptag ctag hp hc (.succ depth) rest token raw _ hi etag he
   exact ⟨h.discharge.finish⟩
 · have hd := successorDepth p [] ptag ctag hp hc (Term.numeral 2) depth rest depth raw
   have hi := equalCase p [] (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) depth raw hd
   obtain ⟨h⟩ := enterIndex p [] ptag ctag hp hc (.succ depth) rest depth raw raw hi etag he
   exact ⟨h.finish⟩
 · let T := GorbowPRNumeralCalculation.Theory p
   let H := Formula.equal (.add depth (.succ gap)) token
   let G := [H]
   have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
   have hd := successorDepth p G ptag ctag hp hc (Term.numeral 2) depth rest token raw
   have hi := aboveCase p G (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) token depth gap raw hd hh
   obtain ⟨h⟩ := enterIndex p G ptag ctag hp hc (.succ depth) rest token raw .zero hi etag he
   exact ⟨h.discharge.finish⟩
 · have hd := zeroDepth p [] ptag ctag hp hc rest .zero raw
   have hi := equalCase p [] (stateValue ptag ctag (Term.numeral 2) .zero rest) .zero raw hd
   obtain ⟨h⟩ := enterIndex p [] ptag ctag hp hc .zero rest .zero raw raw hi etag he
   exact ⟨h.finish⟩
 · have hd := zeroDepth p [] ptag ctag hp hc rest (.succ token) raw
   have hi := aboveCase p [] (stateValue ptag ctag (Term.numeral 2) .zero rest) (.succ token) .zero token raw hd
    (.base (zeroLeft (.succ token)))
   obtain ⟨h⟩ := enterIndex p [] ptag ctag hp hc .zero rest (.succ token) raw .zero hi etag he
   exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalProof
