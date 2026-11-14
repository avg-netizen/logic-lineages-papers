module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.CombinatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
variable {n arity ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (args : List.Vector (Term ctx) arity)
theorem rightLine (t u v : Program arity) (tv uv vv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv) :
 Computes p [] (RawAddRightReplace.line t u v) args (RawAddRightReplace.lineCall I.addRightLineTag tv uv vv) := by
 have h := RawAddRightReplace.ConstructorProof.computesLine p [] I.pairTag I.consTag I.appendTag I.hp I.hc I.ha args t u v tv uv vv ht hu hv
 obtain ⟨he⟩ := RawAddRightReplace.StatementChecks.exactInternalLine n p I.addRightLineTag I.pairTag I.consTag I.appendTag I.haddRightLine I.hp I.hc I.ha ctx tv uv vv
 intro tag hh
 obtain ⟨hc⟩ := h tag hh
 exact ⟨localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ he))⟩
theorem rightCompute (t u v cert : Program arity) (tv uv vv cv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv)
 (hv : Computes p [] v args vv) (hc : Computes p [] cert args cv) :
 Computes p [] (rightCongruence t u v cert) args
  (RawAddRightCongruence.certificate I.mpTag I.addRightLineTag I.reflexivityTag I.consTag I.appendTag tv uv vv cv) := by
 let J := I.toEvaluation.toCurrent.toComputation.toEvaluator
 have htv := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ ht hv
 have huv := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ hu hv
 have ho := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 0 _ _ _ _ htv huv
 have hi := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 7 _ _ _ _ (RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 0 _ _ _ _ htv htv) ho
 have hr := RawMulNewestAdditionIteration.CombinatorProof.single p old a x J args _ _ (rightLine p old a x I args _ _ _ _ _ _ ht hu hv)
 have hf := RawMulNewestAdditionIteration.CombinatorProof.single p old a x J args _ _ (RawMulNewestAdditionIteration.CombinatorProof.reflexive p old a x J args _ _ htv)
 exact RawMulNewestAdditionIteration.CombinatorProof.mpCompute p old a x J args _ _ _ _ _ _ ho (RawMulNewestAdditionIteration.CombinatorProof.mpCompute p old a x J args _ _ _ _ _ _ hi hr hc) hf
theorem leftLine (t u v : Program arity) (tv uv vv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv) :
 Computes p [] (RawAddLeftReplace.line t u v) args (RawAddLeftReplace.lineCall I.addLeftLineTag tv uv vv) := by
 have h := RawAddLeftReplace.ConstructorProof.computesLine p [] I.pairTag I.consTag I.appendTag I.hp I.hc I.ha args t u v tv uv vv ht hu hv
 obtain ⟨he⟩ := RawAddLeftReplace.StatementChecks.exactInternalLine n p I.addLeftLineTag I.pairTag I.consTag I.appendTag I.haddLeftLine I.hp I.hc I.ha ctx tv uv vv
 intro tag hh
 obtain ⟨hc⟩ := h tag hh
 exact ⟨localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ he))⟩
theorem leftCompute (t u v cert : Program arity) (tv uv vv cv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv)
 (hv : Computes p [] v args vv) (hc : Computes p [] cert args cv) :
 Computes p [] (leftCongruence t u v cert) args
  (RawAddLeftCongruence.certificate I.mpTag I.addLeftLineTag I.reflexivityTag I.consTag I.appendTag tv uv vv cv) := by
 let J := I.toEvaluation.toCurrent.toComputation.toEvaluator
 have htv := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ hv ht
 have huv := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ hv hu
 have ho := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 0 _ _ _ _ htv huv
 have hi := RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 7 _ _ _ _ (RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 0 _ _ _ _ htv htv) ho
 have hr := RawMulNewestAdditionIteration.CombinatorProof.single p old a x J args _ _ (leftLine p old a x I args _ _ _ _ _ _ ht hu hv)
 have hf := RawMulNewestAdditionIteration.CombinatorProof.single p old a x J args _ _ (RawMulNewestAdditionIteration.CombinatorProof.reflexive p old a x J args _ _ htv)
 exact RawMulNewestAdditionIteration.CombinatorProof.mpCompute p old a x J args _ _ _ _ _ _ ho (RawMulNewestAdditionIteration.CombinatorProof.mpCompute p old a x J args _ _ _ _ _ _ hi hr hc) hf
theorem binaryCompute (t t' u u' first second : Program arity) (tv tv' uv uv' f s : Term ctx)
 (ht : Computes p [] t args tv) (ht' : Computes p [] t' args tv')
 (hu : Computes p [] u args uv) (hu' : Computes p [] u' args uv')
 (hf : Computes p [] first args f) (hs : Computes p [] second args s) :
 Computes p [] (binaryCongruence t t' u u' first second) args
  (RawBinaryAdditionCongruence.certificate I.mpTag I.addLeftLineTag I.addRightLineTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag tv tv' uv uv' f s) := by
 let J := I.toEvaluation.toCurrent.toComputation.toEvaluator
 exact RawMulNewestAdditionIteration.CombinatorProof.transitivityCompute p old a x J args _ _ _ _ _ _ _ _ _ _
  (RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ ht hu)
  (RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ ht' hu)
  (RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ ht' hu')
  (rightCompute p old a x I args _ _ _ _ _ _ _ _ ht ht' hu hf)
  (leftCompute p old a x I args _ _ _ _ _ _ _ _ hu hu' ht' hs)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.CombinatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.CombinatorProof
