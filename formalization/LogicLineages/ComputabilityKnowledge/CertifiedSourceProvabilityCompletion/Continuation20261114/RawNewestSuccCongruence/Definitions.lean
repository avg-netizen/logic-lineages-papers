module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryAdditionCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestSuccCongruence
open GorbowPRProgram GorbowPRRegistry
/-- Actual newest checker and both addition congruences; only the original
successor replacement constructor is additionally installed. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toNewestEquality : RawNewestTransitivity.Installation p old a x where
 replaceTag : Nat
 hreplace : (nodes p)[replaceTag]? = some ⟨2,RawSuccReplace.lineConstructor⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestSuccCongruence
