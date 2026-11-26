module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedMulRightCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Same newest checker; additional entries are only the original suffix schema ASTs. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toNewest : RawMulLeftCongruence.Installation p old a x where
 rightLineTag : Nat
 rightTestTag : Nat
 rightSearchTag : Nat
 hrightLine : (nodes p)[rightLineTag]? = some ⟨3,RawMulRightReplace.lineConstructor⟩
 hrightTest : (nodes p)[rightTestTag]? = some ⟨2,RawMulRightReplace.candidateTest⟩
 hrightSearch : (nodes p)[rightSearchTag]? = some ⟨3,RawSuffixSearch.search RawMulRightReplace.candidateTest⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedMulRightCongruence
