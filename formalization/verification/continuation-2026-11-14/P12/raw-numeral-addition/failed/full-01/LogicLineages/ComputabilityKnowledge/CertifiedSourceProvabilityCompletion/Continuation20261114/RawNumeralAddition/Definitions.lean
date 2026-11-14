module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual certificate produced by the checked addition iterator, not a fresh witness. -/
def certificate {ctx : Nat} (it num right : Nat) (m n : Term ctx) : Term ctx :=
 RawIteratedSucc.third right (RawAdditionIteration.binaryCall it n (LiteralNumeralPrefix.numeralCall num m))
def Capability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (m k index fuel : Term ctx), Nonempty (Derivation T
  (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
   (RawAdditionComputation.addRaw I.ctag I.atag (LiteralNumeralPrefix.numeralCall I.numeralTag m)
    (LiteralNumeralPrefix.numeralCall I.numeralTag k))
   (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
   (certificate I.iteratorTag I.numeralTag I.rightTag m k)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition
