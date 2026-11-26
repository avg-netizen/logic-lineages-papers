module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeDNE
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeRule
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionStepProgram.NativeOperations CurrentRecursionBaseProgram.TransitivityNativeProof CurrentRecursionBaseProgram.NativePrimitives
open NativeSyntax NativeCompose NativeDNE HistoryRuleSuffix.NativeProof
theorem ruleEval {arity : Nat} (a witness : Program arity) (v : List.Vector Nat arity) (A : Formula 1) (t : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (ht : evaluate witness v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (rule a witness) v = ruleNumber A t := by
 let P := A.neg.all
 let I := GorbowStandardInstances.instantiate A t
 let pp := allCode (neg a)
 let ii := instantiateCode a witness
 have hna := negEval a v A ha
 have hP := allEval (neg a) v A.neg hna
 have hI := instanceEval a witness v A t ha ht
 have hnP := negEval pp v P hP
 have hnnP := negEval (neg pp) v P.neg hnP
 have hnI := negEval ii v I hI
 let inst := CurrentRecursionBaseProgram.allInstance (neg a) witness
 let dne := doubleNegation pp
 let bridge := compose (neg (neg pp)) pp (neg ii) inst dne
 let contra := logicalSingleton false (neg pp) ii
 let negative := CurrentRecursionBaseProgram.mp (imp ii (neg pp)) contra bridge
 let dual := logicalSingleton true a (constant arity 0)
 have hinst : evaluate inst v = logicalNumber (.allInstantiate A.neg t) := allInstanceEval _ _ v A.neg t hna ht
 have hdne : evaluate dne v = doubleNegationNumber P := doubleNegationEval pp v P hP
 have hbridge : evaluate bridge v = composeNumber P.neg.neg P I.neg
  (logicalNumber (.allInstantiate A.neg t)) (doubleNegationNumber P) := by
  rw [show bridge = compose (neg (neg pp)) pp (neg ii) inst dne from rfl,
   composeEval _ _ _ _ _ v P.neg.neg P I.neg hnnP hP hnI,hinst,hdne]
 have hcontra : evaluate contra v = logicalNumber (.classicalContraposition P.neg I) := classicalEval _ _ v _ _ hnP hI
 have hnegative : evaluate negative v = GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode (.imp I P.neg))
  (logicalNumber (.classicalContraposition P.neg I))
  (composeNumber P.neg.neg P I.neg (logicalNumber (.allInstantiate A.neg t)) (doubleNegationNumber P)) := by
  rw [show negative = CurrentRecursionBaseProgram.mp (imp ii (neg pp)) contra bridge from rfl,
   mpEval _ _ _ v (.imp I P.neg) (impEval _ _ v I P.neg hI hnP),hcontra,hbridge]
 have hdual : evaluate dual v = logicalNumber (.existsDualBackward A) := existentialEval _ _ v A ha
 change evaluate (compose ii (neg pp) (exCode a) dual negative) v = _
 rw [composeEval _ _ _ _ _ v I P.neg A.ex hI hnP (exEval a v A ha),hdual,hnegative]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeRule
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeRule
