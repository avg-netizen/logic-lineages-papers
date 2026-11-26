module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113
/-- No new parser, encoding or semantic oracle: these are the existing literal
PR append, repeated-tail, true list-length and checked suffix-search programs. -/
structure Installation {n : Nat} (p : Program n) (test : Program 2) extends
 RawSuffixSearch.Installation p test where
 lengthTag : Nat
 appendTag : Nat
 consTag : Nat
 hl : (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩
 ha : (nodes p)[appendTag]? = some ⟨2,HistoryAppend.append⟩
 hc : (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence
