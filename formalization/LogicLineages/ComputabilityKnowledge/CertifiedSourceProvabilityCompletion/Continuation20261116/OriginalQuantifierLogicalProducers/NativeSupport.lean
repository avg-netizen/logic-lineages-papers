module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
def nativeConclusion (isExists : Bool) (a b : List Nat) : List Nat :=
 if isExists then GorbowCodeConstructors.binary 7
  (GorbowCodeConstructors.unary 6 (GorbowCodeConstructors.unary 10 (GorbowCodeConstructors.unary 6 a)))
  (GorbowCodeConstructors.unary 11 a)
 else GorbowCodeConstructors.binary 7
  (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.unary 6 a) (GorbowCodeConstructors.unary 6 b))
  (GorbowCodeConstructors.binary 7 b a)
def nativeLine (isExists : Bool) (a b : List Nat) : GorbowProofChecker.Line :=
 (0,nativeConclusion isExists a b,0,(if isExists then 10 else 2),(if isExists then [a] else [a,b]),0,0)

theorem consAt (x y : Nat) : evaluate HistoryCodec.cons (x ::ᵥ y ::ᵥ nil) = (Nat.pair x y).succ :=
 HistoryCodec.NativeProof.nativeConsAllVectors _

theorem unaryAt {n : Nat} (tag : Nat) (f : Program n) (v : List.Vector Nat n) (a : List Nat)
 (ha : evaluate f v = Encodable.encode a) :
 evaluate (FixedFormulaSubstitution.unary tag f) v = Encodable.encode (GorbowCodeConstructors.unary tag a) := by
 simp only [FixedFormulaSubstitution.unary,twoEval,constantEval,ha,consAt]
 rfl

theorem conclusionAt {n : Nat} (isExists : Bool) (f g : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b) :
 evaluate (conclusion isExists f g) v = Encodable.encode (nativeConclusion isExists a b) := by
 cases isExists with
 | false =>
  exact UniformClosedPropositional.NativeLineProof.binaryAt 7 _ _ v _ _
   (UniformClosedPropositional.NativeLineProof.binaryAt 7 _ _ v _ _ (unaryAt 6 f v a ha) (unaryAt 6 g v b hb))
   (UniformClosedPropositional.NativeLineProof.binaryAt 7 g f v b a hb ha)
 | true =>
  exact UniformClosedPropositional.NativeLineProof.binaryAt 7 _ _ v _ _
   (unaryAt 6 _ v _ (unaryAt 10 _ v _ (unaryAt 6 f v a ha)))
   (unaryAt 11 f v a ha)

theorem argumentsAt {n : Nat} (isExists : Bool) (f g : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b) :
 evaluate (arguments isExists f g) v = Encodable.encode (if isExists then [a] else [a,b]) := by
 cases isExists <;> simp only [arguments,Bool.false_eq_true,if_false,if_true,twoEval,ha,hb,constantEval,consAt] <;> rfl

theorem lineAt {n : Nat} (isExists : Bool) (f g : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b) :
 evaluate (line isExists f g) v = Encodable.encode (nativeLine isExists a b) := by
 simp only [line,twoEval,constantEval,conclusionAt isExists f g v a b ha hb,
  argumentsAt isExists f g v a b ha hb,pairEval]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeSupport
