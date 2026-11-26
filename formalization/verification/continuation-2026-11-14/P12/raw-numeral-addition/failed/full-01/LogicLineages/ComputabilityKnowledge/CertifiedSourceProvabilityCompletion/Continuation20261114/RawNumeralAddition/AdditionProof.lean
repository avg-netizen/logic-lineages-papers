module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.PrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.AdditionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowSubstitution GorbowFormulaSubstitution
theorem internalAddition : Targets.InternalAddition := by
 intro n p old a x I ctx m k index fuel
 obtain ⟨hv⟩ := RawAdditionIteration.InvariantSupport.numeralValid p old a x I m
 obtain ⟨hit⟩ := RawAdditionIteration.StatementChecks.exactIteration n p old a x I ctx k
  (LiteralNumeralPrefix.numeralCall I.numeralTag m) index fuel
 have hstate := Derivation.mp hit hv
 have htail := Derivation.mp (.logical (.andRight _ _)) hstate
 have hc := Derivation.mp (.logical (.andRight _ _)) htail
 obtain ⟨he⟩ := PrefixProof.internalPrefixNumeral n p old a x I ctx m k
 have hm := RawAdditionIteration.InvariantSupport.moveSecond
  I.vtag I.qctag I.ctag I.atag index fuel (LiteralNumeralPrefix.numeralCall I.numeralTag m)
  (LiteralNumeralPrefix.numeralCall I.numeralTag k)
  (RawAdditionIteration.binaryCall I.prefixTag k (LiteralNumeralPrefix.numeralCall I.numeralTag m))
  (certificate I.iteratorTag I.numeralTag I.rightTag m k)
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
 have hout := Derivation.mp (Derivation.mp hm he) hc
 exact ⟨Derivation.mp (.logical (.andRight _ _)) hout⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.AdditionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.AdditionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.AdditionProof.internalAddition
