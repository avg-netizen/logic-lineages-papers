module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem left {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (pF : Program 1) (c : Code) (sigma : Sentence) (innerFuel innerCert : Term ctx) :
 ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((leftArgs (tags I.previous) pF c sigma innerFuel innerCert).get i))) := by
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old a x I
 have hn (v : Term ctx) := PrescribedRuntimeCallCongruence.ValidityProof.numeral p (CumulativeUniformRule12Registry.previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.previous.current
  (tags I.previous).numeralTag H.hn G v
 intro i
 refine Fin.cases ?_ (fun i => ?_) i
 · exact hn _
 · refine Fin.cases ?_ (fun i => ?_) i
   · exact hn _
   · refine Fin.cases ?_ (fun i => ?_) i
     · exact hn _
     · refine Fin.cases ?_ (fun i => ?_) i
       · exact PrescribedRuntimeCallCongruence.ValidityProof.closed p (CumulativeUniformRule12Registry.previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.previous.current G (argument pF c sigma)
       · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
         exact hn _

theorem right {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (pF : Program 1) (c : Code) (sigma : Sentence) (innerFuel innerCert : Term ctx) :
 ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((rightArgs (tags I.previous) pF c sigma innerFuel innerCert).get i))) := by
 intro i
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old a x I
 simpa only [rightArgs,List.Vector.get_map] using
  PrescribedRuntimeCallCongruence.ValidityProof.numeral p (CumulativeUniformRule12Registry.previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.previous.current
   (tags I.previous).numeralTag H.hn G ((CurrentCheckerSuccessCertificate.checkerInputs c innerFuel (value pF c sigma) innerCert).get i)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ValidityProof
