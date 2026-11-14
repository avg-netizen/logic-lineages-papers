module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.CombinatorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem internalGraph : Targets.InternalGraph := by
 intro n p old a x I ctx t u m k first second
 let args := t ::ᵥ u ::ᵥ m ::ᵥ k ::ᵥ first ::ᵥ second ::ᵥ nil
 let J := I.toEvaluation.toCurrent.toComputation.toEvaluator
 let K := I.toEvaluation.toCurrent
 have ht := projection p [] args 0
 have hu := projection p [] args 1
 have hm := projection p [] args 2
 have hk := projection p [] args 3
 have hf := projection p [] args 4
 have hs := projection p [] args 5
 have hnm := RawNewestMultiplicationIteration.CombinatorProof.numeral p old a x K args _ _ hm
 have hnk := RawNewestMultiplicationIteration.CombinatorProof.numeral p old a x K args _ _ hk
 have hsum := RawNewestMultiplicationIteration.CombinatorProof.next p args _ _ _ _ hk hm
 have hans := RawNewestMultiplicationIteration.CombinatorProof.numeral p old a x K args _ _ hsum
 have hraw := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ ht hu
 have hnums := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ hnm hnk
 have hcon := CombinatorProof.binaryCompute p old a x I args _ _ _ _ _ _ _ _ _ _ _ _ ht hnm hu hnk hf hs
 have hit := binary p [] args RawAdditionIteration.iterator _ _ _ _ _ hk hnm
  (copies p [] RawAdditionIteration.iterator I.iteratorTag I.hiterator _)
 have hcert := RawNewestMultiplicationIteration.CombinatorProof.third p old a x K args _ _ hit
 obtain ⟨h⟩ := RawMulNewestAdditionIteration.CombinatorProof.transitivityCompute p old a x J args
  _ _ _ _ _ _ _ _ _ _ hraw hnums hans hcon hcert I.producerTag I.hproducer
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.GraphProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.GraphProof.internalGraph
