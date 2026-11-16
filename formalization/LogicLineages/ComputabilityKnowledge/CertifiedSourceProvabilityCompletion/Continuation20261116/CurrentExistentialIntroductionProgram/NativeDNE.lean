module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeCompose
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeDNE
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionStepProgram.NativeOperations CurrentRecursionBaseProgram.TransitivityNativeProof
open NativeSyntax NativeCompose HistoryRuleSuffix.NativeProof
theorem doubleNegationEval {arity : Nat} (p : Program arity) (v : List.Vector Nat arity) (P : Formula 0)
 (hp : evaluate p v = Encodable.encode (GorbowFormulaPrefixCode.encode P)) :
 evaluate (doubleNegation p) v = doubleNegationNumber P := by
 let R : Formula 0 := .equal .zero .zero
 let r : Program arity := constant arity (Encodable.encode (GorbowFormulaPrefixCode.encode R))
 let A := P.neg.neg
 let a := neg (neg p)
 have hr : evaluate r v = Encodable.encode (GorbowFormulaPrefixCode.encode R) := constantEval _ _ _
 have hnp := negEval p v P hp
 have hnr := negEval r v R hr
 have ha := negEval (neg p) v P.neg hnp
 have hnnr := negEval (neg r) v R.neg hnr
 let c1 := logicalSingleton false (neg r) (neg p)
 let k := CurrentRecursionStepProgram.propositional false a (neg (neg r)) a
 let first := compose a (imp (neg (neg r)) a) (imp (neg p) (neg r)) c1 k
 let c2 := logicalSingleton false p r
 let second := compose a (imp (neg p) (neg r)) (imp r p) c2 first
 let truth := CurrentRecursionStepProgram.reflexivity
  (constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.zero : Term 0))))
 have hc1 : evaluate c1 v = logicalNumber (.classicalContraposition R.neg P.neg) := classicalEval _ _ v _ _ hnr hnp
 have hk : evaluate k v = UniformClosedPropositional.singletonNumber false A R.neg.neg A :=
  propositionalEval false _ _ _ v A R.neg.neg A ha hnnr ha
 have hfirst : evaluate first v = composeNumber A (.imp R.neg.neg A) (.imp P.neg R.neg)
  (logicalNumber (.classicalContraposition R.neg P.neg)) (UniformClosedPropositional.singletonNumber false A R.neg.neg A) := by
  rw [show first = compose a (imp (neg (neg r)) a) (imp (neg p) (neg r)) c1 k from rfl,
   composeEval _ _ _ _ _ v A (.imp R.neg.neg A) (.imp P.neg R.neg) ha
    (impEval _ _ v _ _ hnnr ha) (impEval _ _ v _ _ hnp hnr),hc1,hk]
 have hc2 : evaluate c2 v = logicalNumber (.classicalContraposition P R) := classicalEval _ _ v _ _ hp hr
 have hsecond : evaluate second v = composeNumber A (.imp P.neg R.neg) (.imp R P)
  (logicalNumber (.classicalContraposition P R))
  (composeNumber A (.imp R.neg.neg A) (.imp P.neg R.neg)
   (logicalNumber (.classicalContraposition R.neg P.neg)) (UniformClosedPropositional.singletonNumber false A R.neg.neg A)) := by
  rw [show second = compose a (imp (neg p) (neg r)) (imp r p) c2 first from rfl,
   composeEval _ _ _ _ _ v A (.imp P.neg R.neg) (.imp R P) ha
    (impEval _ _ v _ _ hnp hnr) (impEval _ _ v _ _ hr hp),hc2,hfirst]
 have htruth : evaluate truth v = logicalNumber (.reflexive .zero) :=
  reflexivityEval _ v .zero (constantEval _ _ _)
 change evaluate (CurrentRecursionStepProgram.mpUnderProgram a r p second
  (CurrentRecursionStepProgram.liftProgram r a truth)) v = _
 rw [mpUnderEval _ _ _ _ _ v A R P ha hr hp,
  liftEval _ _ _ v R A hr ha,hsecond,htruth]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeDNE
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeDNE
