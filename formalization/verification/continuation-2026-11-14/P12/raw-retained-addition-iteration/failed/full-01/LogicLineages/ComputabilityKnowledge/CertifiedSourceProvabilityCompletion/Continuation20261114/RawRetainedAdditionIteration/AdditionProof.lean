module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.PrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.AdditionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowSubstitution GorbowFormulaSubstitution
theorem internalAddition : Targets.InternalNumeralAddition := by
 intro n p old a x I ctx m k index fuel
 obtain ⟨hv⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I m
 obtain ⟨hit⟩ := IterationProof.internalIteration n p old a x I ctx k
  (LiteralNumeralPrefix.numeralCall I.numeralTag m) index fuel
 have hstate := Derivation.mp hit hv
 have htail := Derivation.mp (.logical (.andRight _ _)) hstate
 have hc := Derivation.mp (.logical (.andRight _ _)) htail
 obtain ⟨he⟩ := PrefixProof.internalPrefixNumeral n p old a x I ctx m k
 have hm := RawRetainedAdditionIteration.InvariantSupport.moveSecond (T := GorbowPRNumeralCalculation.Theory p)
  I.vtag I.qctag I.ctag I.atag index fuel (LiteralNumeralPrefix.numeralCall I.numeralTag m)
  (LiteralNumeralPrefix.numeralCall I.numeralTag k)
  (RawRetainedAdditionIteration.binaryCall I.prefixTag k (LiteralNumeralPrefix.numeralCall I.numeralTag m))
  (RawIteratedSucc.third I.rightTag (binaryCall I.iteratorTag k (LiteralNumeralPrefix.numeralCall I.numeralTag m)))
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
 have hout := Derivation.mp (Derivation.mp hm he) hc
 exact ⟨Derivation.mp (.logical (.andRight _ _)) hout⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.AdditionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.AdditionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.AdditionProof.internalAddition
