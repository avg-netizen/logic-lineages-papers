module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.ConstructorStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.EquationsProof
open RawAdditionIteration (binaryCall unaryCall)
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem iteratorZero {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.mulIteratorTag .zero t) (unaryCall I.mulBaseTag t))) := by
 let st : Program 3 := applyTwo step (.projection 2) (.projection 1)
 have hb := GorbowPRSubtree.Proof.lookupTransport n p I.mulIteratorTag ⟨2,iterator⟩ 1 ⟨1,base⟩ I.hmulIterator
  (GorbowPRChildTags.Proof.recursionBase 1 base st)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p I.mulIteratorTag 1 base st I.hmulIterator ctx (t ::ᵥ nil)
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (I.mulIteratorTag+1) I.mulBaseTag 1 base hb I.hmulBase ctx (t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hc⟩

theorem iteratorSuccessor {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.mulIteratorTag (.succ count) t)
   (binaryCall I.mulStepTag t (binaryCall I.mulIteratorTag count t)))) := by
 let st : Program 3 := applyTwo step (.projection 2) (.projection 1)
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.mulIteratorTag base st I.hmulIterator
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.mulIteratorTag 1 base st I.hmulIterator ctx count (t ::ᵥ nil)
 let previous := binaryCall I.mulIteratorTag count t
 let args := count ::ᵥ previous ::ᵥ t ::ᵥ nil
 obtain ⟨he⟩ := binary p [] args step (.projection 2) (.projection 1) t previous (binaryCall I.mulStepTag t previous)
  (projection p [] args 2) (projection p [] args 1) (copies p [] step I.mulStepTag I.hmulStep (t ::ᵥ previous ::ᵥ nil))
  (I.mulIteratorTag+GorbowPRChildTags.stepTag base) hs
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base hr) he)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.EquationsProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.EquationsProof.iteratorZero
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.EquationsProof.iteratorSuccessor
