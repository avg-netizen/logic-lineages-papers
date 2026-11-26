module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeLineProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem binaryAt {n : Nat} (tag : Nat) (f g : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b) :
 evaluate (FixedFormulaSubstitution.binary tag f g) v = Encodable.encode (GorbowCodeConstructors.binary tag a b) := by
 have hc (x y : Nat) : evaluate HistoryCodec.cons (x ::ᵥ y ::ᵥ nil) = (Nat.pair x y).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 simp only [FixedFormulaSubstitution.binary,FixedFormulaSubstitution.unary,twoEval,constantEval,ha,hb,appendList,hc]
 rfl
theorem argumentsAt {n : Nat} (isS : Bool) (f g h : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b)
 (hc : evaluate h v = Encodable.encode c) :
 evaluate (arguments isS f g h) v = Encodable.encode (if isS then [a,b,c] else [a,b]) := by
 have hcons (x y : Nat) : evaluate HistoryCodec.cons (x ::ᵥ y ::ᵥ nil) = (Nat.pair x y).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 cases isS <;> simp only [arguments,Bool.false_eq_true,if_false,if_true,twoEval,ha,hb,hc,constantEval,hcons] <;> rfl
theorem conclusionAt {n : Nat} (isS : Bool) (f g h : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b)
 (hc : evaluate h v = Encodable.encode c) :
 evaluate (conclusion isS f g h) v = Encodable.encode (nativeConclusion isS a b c) := by
 cases isS with
 | false =>
  exact binaryAt 7 f _ v a _ ha (binaryAt 7 g f v b a hb ha)
 | true =>
  exact binaryAt 7 _ _ v _ _
   (binaryAt 7 f _ v a _ ha (binaryAt 7 g h v b c hb hc))
   (binaryAt 7 _ _ v _ _ (binaryAt 7 f g v a b ha hb) (binaryAt 7 f h v a c ha hc))
theorem lineAt {n : Nat} (isS : Bool) (f g h : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate g v = Encodable.encode b)
 (hc : evaluate h v = Encodable.encode c) :
 evaluate (line isS f g h) v = Encodable.encode (nativeLine isS a b c) := by
 simp only [line,twoEval,constantEval,conclusionAt isS f g h v a b c ha hb hc,
  argumentsAt isS f g h v a b c ha hb hc,pairEval]
 rfl
theorem exactNativeLine : Targets.NativeLine := by
 intro isS a b c
 exact lineAt isS (.projection 0) (.projection 1) (.projection 2)
  (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ Encodable.encode c ::ᵥ nil) a b c rfl rfl rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeLineProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeLineProof
