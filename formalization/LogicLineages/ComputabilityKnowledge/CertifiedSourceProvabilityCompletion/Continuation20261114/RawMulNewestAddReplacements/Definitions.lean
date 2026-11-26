module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual registry slots for both original addition contexts; the entire newest
multiplication computation interface and checker are retained at identical addresses. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toCurrent : RawMultiplicationEvaluation.Installation p old a x where
 addRightLineTag : Nat
 haddRightLine : (nodes p)[addRightLineTag]? = some ⟨3,RawAddRightReplace.lineConstructor⟩
 addRightTestTag : Nat
 haddRightTest : (nodes p)[addRightTestTag]? = some ⟨2,RawAddRightReplace.candidateTest⟩
 addRightSearchTag : Nat
 haddRightSearch : (nodes p)[addRightSearchTag]? = some ⟨3,RawSuffixSearch.search RawAddRightReplace.candidateTest⟩
 addLeftLineTag : Nat
 haddLeftLine : (nodes p)[addLeftLineTag]? = some ⟨3,RawAddLeftReplace.lineConstructor⟩
 addLeftTestTag : Nat
 haddLeftTest : (nodes p)[addLeftTestTag]? = some ⟨2,RawAddLeftReplace.candidateTest⟩
 addLeftSearchTag : Nat
 haddLeftSearch : (nodes p)[addLeftSearchTag]? = some ⟨2,RawNumericSearch.search RawAddLeftReplace.candidateTest⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements
