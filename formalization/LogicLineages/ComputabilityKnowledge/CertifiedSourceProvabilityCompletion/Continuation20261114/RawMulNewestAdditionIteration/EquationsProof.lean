module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem iteratorZero {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.iteratorTag .zero t) (unaryCall I.baseTag t))) := by
 let st : Program 3 := applyTwo step (.projection 2) (.projection 1)
 have hb := GorbowPRSubtree.Proof.lookupTransport n p I.iteratorTag ⟨2,iterator⟩ 1 ⟨1,base⟩ I.hiterator
  (GorbowPRChildTags.Proof.recursionBase 1 base st)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p I.iteratorTag 1 base st I.hiterator ctx (t ::ᵥ nil)
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (I.iteratorTag+1) I.baseTag 1 base hb I.hbase ctx (t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hc⟩

theorem iteratorSuccessor {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.iteratorTag (.succ count) t)
   (binaryCall I.stepTag t (binaryCall I.iteratorTag count t)))) := by
 let st : Program 3 := applyTwo step (.projection 2) (.projection 1)
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.iteratorTag base st I.hiterator
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.iteratorTag 1 base st I.hiterator ctx count (t ::ᵥ nil)
 let previous := binaryCall I.iteratorTag count t
 let args := count ::ᵥ previous ::ᵥ t ::ᵥ nil
 obtain ⟨he⟩ := binary p [] args step (.projection 2) (.projection 1) t previous (binaryCall I.stepTag t previous)
  (projection p [] args 2) (projection p [] args 1) (copies p [] step I.stepTag I.hstep (t ::ᵥ previous ::ᵥ nil))
  (I.iteratorTag+GorbowPRChildTags.stepTag base) hs
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base hr) he)⟩

theorem prefixZero {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.prefixTag .zero t) t)) := by
 let b : Program 1 := .projection 0
 let st : Program 3 := RawAddSucc.successorRaw (.projection 1)
 have hb := GorbowPRSubtree.Proof.lookupTransport n p I.prefixTag ⟨2,successorPrefix⟩ 1 ⟨1,b⟩ I.hprefix
  (GorbowPRChildTags.Proof.recursionBase 1 b st)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p I.prefixTag 1 b st I.hprefix ctx (t ::ᵥ nil)
 obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (I.prefixTag+1) (0 : Fin 1) hb (t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hp⟩

theorem prefixSuccessor {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.prefixTag (.succ count) t)
   (RawAdditionComputation.succRaw I.consTag (binaryCall I.prefixTag count t)))) := by
 let b : Program 1 := .projection 0
 let st : Program 3 := RawAddSucc.successorRaw (.projection 1)
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.prefixTag b st I.hprefix
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.prefixTag 1 b st I.hprefix ctx count (t ::ᵥ nil)
 let previous := binaryCall I.prefixTag count t
 let args := count ::ᵥ previous ::ᵥ t ::ᵥ nil
 obtain ⟨he⟩ := binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args 2)
  (projection p [] args 1) (copies p [] HistoryCodec.cons I.consTag I.hc _)
  (I.prefixTag+GorbowPRChildTags.stepTag b) hs
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base hr) he)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof.iteratorZero
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof.iteratorSuccessor
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof.prefixZero
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.EquationsProof.prefixSuccessor
