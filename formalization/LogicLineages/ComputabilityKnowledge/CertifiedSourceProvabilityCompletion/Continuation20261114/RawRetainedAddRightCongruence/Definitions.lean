module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddRightCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Same newest checker; additional entries are only the original suffix schema ASTs. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toNewest : RawAddLeftCongruence.Installation p old a x where
 rightLineTag : Nat
 rightTestTag : Nat
 rightSearchTag : Nat
 hrightLine : (nodes p)[rightLineTag]? = some ⟨3,RawAddRightReplace.lineConstructor⟩
 hrightTest : (nodes p)[rightTestTag]? = some ⟨2,RawAddRightReplace.candidateTest⟩
 hrightSearch : (nodes p)[rightSearchTag]? = some ⟨3,RawSuffixSearch.search RawAddRightReplace.candidateTest⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddRightCongruence
