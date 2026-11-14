module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113
structure Installation {n : Nat} (p : Program n) (old : Program 1) extends
 toSearch : RawNumericSearch.Installation p RawAddLeftReplace.candidateTest where
 qtag : Nat
 logicalTag : Nat
 pairTag : Nat
 consTag : Nat
 appendTag : Nat
 lengthTag : Nat
 dropTag : Nat
 validatorTag : Nat
 hq : (nodes p)[qtag]? = some ⟨3,RawAddLeftReplace.lineConstructor⟩
 hlogical : (nodes p)[logicalTag]? = some ⟨1,RawAddLeftReplace.logicalLeaf old⟩
 hp : (nodes p)[pairTag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[consTag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[appendTag]? = some ⟨2,HistoryAppend.append⟩
 hlength : (nodes p)[lengthTag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩
 hdrop : (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩
 hv : (nodes p)[validatorTag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftAcceptance
