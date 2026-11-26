module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence
open GorbowPRProgram GorbowPRRegistry
/-- Identical newest checker and all equality-composition nodes, with the
original binary successor-replacement constructor installed as well. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toEquality : RawEqualityComposition.Installation p old a x where
 replaceTag : Nat
 hreplace : (nodes p)[replaceTag]? = some ⟨2,RawSuccReplace.lineConstructor⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence
