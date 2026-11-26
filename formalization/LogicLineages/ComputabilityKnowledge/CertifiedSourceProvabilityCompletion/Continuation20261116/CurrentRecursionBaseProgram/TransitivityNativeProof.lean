module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativePrimitives
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityNativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality
open NativePrimitives GorbowSubstitution

theorem binaryEval {arity : Nat} (opcode : Nat) (a b : Program arity) (v : List.Vector Nat arity) (xs ys : List Nat)
 (ha : evaluate a v = Encodable.encode xs) (hb : evaluate b v = Encodable.encode ys) :
 evaluate (FixedFormulaSubstitution.binary opcode a b) v = Encodable.encode (opcode :: (xs ++ ys)) := by
 simp only [FixedFormulaSubstitution.binary,FixedFormulaSubstitution.unary,twoEval,constantEval,ha,hb,appendList,
  consEval,HistoryLookup.NativeProof.encodeCons]
 rfl

theorem equalEval {arity : Nat} (a b : Program arity) (v : List.Vector Nat arity) (t u : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode t))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate (FixedFormulaSubstitution.binary 0 a b) v = Encodable.encode (GorbowFormulaPrefixCode.encode (.equal t u)) :=
 binaryEval 0 a b v _ _ ha hb

theorem impEval {arity : Nat} (a b : Program arity) (v : List.Vector Nat arity) (f g : Formula 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode f))
 (hb : evaluate b v = Encodable.encode (GorbowFormulaPrefixCode.encode g)) :
 evaluate (FixedFormulaSubstitution.binary 7 a b) v = Encodable.encode (GorbowFormulaPrefixCode.encode (.imp f g)) :=
 binaryEval 7 a b v _ _ ha hb

theorem matrix (t : Term 0) :
 substituteFormula (liftSubstitute (fun _ : Fin 1 => t)) (.equal (.var 1) (.var 0) : Formula 2) =
 (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0) : Formula 1) := by
 change Formula.equal (renameTerm Fin.succ t) (.var 0) = _
 congr 1
 unfold renameTerm GorbowClosedEquality.liftClosedTerm
 congr 1
 funext i
 exact Fin.elim0 i

theorem transitivityEval {arity : Nat} (a b c first second : Program arity) (v : List.Vector Nat arity)
 (t u w : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode t))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode u))
 (hc : evaluate c v = Encodable.encode (GorbowTermPrefixCode.encode w)) :
 evaluate (transitivity a b c first second) v =
 transitivityNumber t u w (evaluate first v) (evaluate second v) := by
 have htw := equalEval a c v t w ha hc
 have htu := equalEval a b v t u ha hb
 have hmatrix := headQuoteEval (.equal (.var 1) (.var 0) : Formula 2) (fun _ => a) v (fun _ : Fin 1 => t) (fun _ => ha)
 rw [matrix] at hmatrix
 unfold transitivity
 rw [mpEval _ _ _ v _ htw,mpEval _ _ _ v _ (impEval _ _ v _ _ htu htw)]
 rw [replacementEval _ _ _ v _ _ _ hmatrix hb hc]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityNativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityNativeProof
