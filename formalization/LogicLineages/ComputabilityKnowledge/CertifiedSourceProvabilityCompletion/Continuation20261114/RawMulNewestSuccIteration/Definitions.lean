module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
abbrev leftRaw := @RawIteratedSucc.leftRaw
abbrev rightRaw := @RawIteratedSucc.rightRaw
abbrev inputCertificate := @RawIteratedSucc.inputCertificate
abbrev mp := @RawIteratedSucc.mp
abbrev outputRaw := @RawIteratedSucc.outputRaw
abbrev selfRaw := @RawIteratedSucc.selfRaw
abbrev intermediateRaw := @RawIteratedSucc.intermediateRaw
abbrev replacementCertificate := @RawIteratedSucc.replacementCertificate
abbrev reflexivityCertificate := @RawIteratedSucc.reflexivityCertificate
abbrev outputCertificate := @RawIteratedSucc.outputCertificate
abbrev step := @RawIteratedSucc.step
abbrev iterator := @RawIteratedSucc.iterator
abbrev state := @RawIteratedSucc.state
abbrev stepCall := @RawIteratedSucc.stepCall
abbrev iteratorCall := @RawIteratedSucc.iteratorCall
abbrev first := @RawIteratedSucc.first
abbrev second := @RawIteratedSucc.second
abbrev third := @RawIteratedSucc.third
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toCongruence : RawMulNewestSuccCongruence.Installation p old a x where
 rightTag : Nat
 leftTag : Nat
 stepTag : Nat
 iteratorTag : Nat
 prefixTag : Nat
 hright : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩
 hleft : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hstep : (nodes p)[stepTag]? = some ⟨1,step⟩
 hiterator : (nodes p)[iteratorTag]? = some ⟨2,iterator⟩
 hprefix : (nodes p)[prefixTag]? = some ⟨2,RawAdditionIteration.successorPrefix⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration
