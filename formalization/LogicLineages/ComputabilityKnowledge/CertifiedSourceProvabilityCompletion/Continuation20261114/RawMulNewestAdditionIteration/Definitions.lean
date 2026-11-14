module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddition.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
abbrev mp := @RawAdditionIteration.mp
abbrev singleton := @RawAdditionIteration.singleton
abbrev eqRaw := @RawAdditionIteration.eqRaw
abbrev transport := @RawAdditionIteration.transport
abbrev symmetry := @RawAdditionIteration.symmetry
abbrev transitivity := @RawAdditionIteration.transitivity
abbrev congruence := @RawAdditionIteration.congruence
abbrev computation := @RawAdditionIteration.computation
abbrev stateRaw := @RawAdditionIteration.stateRaw
abbrev base := @RawAdditionIteration.base
abbrev currentNumeral := @RawAdditionIteration.currentNumeral
abbrev currentValue := @RawAdditionIteration.currentValue
abbrev currentCertificate := @RawAdditionIteration.currentCertificate
abbrev step := @RawAdditionIteration.step
abbrev iterator := @RawAdditionIteration.iterator
abbrev successorPrefix := @RawAdditionIteration.successorPrefix
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toAddition : RawMulNewestAddition.Installation p old a x where
 rightTag : Nat
 leftTag : Nat
 baseTag : Nat
 stepTag : Nat
 iteratorTag : Nat
 numeralTag : Nat
 prefixTag : Nat
 hright : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩
 hleft : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hbase : (nodes p)[baseTag]? = some ⟨1,base⟩
 hstep : (nodes p)[stepTag]? = some ⟨2,step⟩
 hiterator : (nodes p)[iteratorTag]? = some ⟨2,iterator⟩
 hnumeral : (nodes p)[numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hprefix : (nodes p)[prefixTag]? = some ⟨2,successorPrefix⟩
def unaryCall {ctx : Nat} (tag : Nat) (t : Term ctx) : Term ctx := call tag (t ::ᵥ nil)
def binaryCall {ctx : Nat} (tag : Nat) (t u : Term ctx) : Term ctx := call tag (t ::ᵥ u ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration
