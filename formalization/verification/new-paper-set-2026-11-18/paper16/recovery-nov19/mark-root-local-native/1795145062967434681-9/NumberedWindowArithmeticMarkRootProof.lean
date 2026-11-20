import LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootProof
open NumberedWindowArithmeticMarkRootTargets NumberedWindowMarkRootAlgorithm
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowSyntax NumberedWindowRawWitnessRootBits NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticRawRootCode

private theorem actual (S K w) (f : Nat → Nat → Bool)
    (h : ∀ q r, f (encodeTerm q) (encodeTerm r) = rootBit S K w q r) (a b : Nat) :
    guarded a b (f a b) = rootOn S K w a b := by
  unfold guarded rootOn between
  rw [NumberedWindowArithmeticRawRootCodeProof.rootRound,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards]
  simp only [NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow]
  cases ha : decodeTerm a with
  | none => rfl
  | some q =>
    cases hb : decodeTerm b with
    | none => rfl
    | some r =>
      rw [← (exact_TermCodec.1 a q).mp ha,← (exact_TermCodec.1 b r).mp hb]
      exact h q r

private theorem readNode (i : Nat) (fs : List Nat) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeNode i fs) = some (i,fs) := by
  rw [← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2]
  exact NumberedWindowArithmeticNodeProof.nodeRound _ _

private theorem markCode (f t k bs es r) :
    (NumberedWindowFieldAlgorithm.packNode 5 [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es] ==
      encodeTerm r) = NumberedWindowLiteralEquality.termEq (.numbered f t k bs es) r :=
  NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.1 _ _

theorem markEq : ExactMarkRoot := by
  intro S K k
  funext a b
  apply actual
  intro q r
  cases q <;> simp [encodeTerm,readNode,markBody,rootBit,List.getD_eq_getElem?_getD,
    NumberedWindowArithmeticAnnotationProof.head]
  rename_i f bs
  exact markCode f f.result k bs .nil r

theorem lowerEq : ExactLowerRoot := by
  intro S K
  funext a b
  apply actual
  intro q r
  cases q <;> simp [encodeTerm,readNode,lowerBody,rootBit,List.getD_eq_getElem?_getD]
  rename_i f t k bs es
  cases k with
  | zero => rfl
  | succ k => exact markCode f t k bs es r

theorem bottomEq : ExactBottomRoot := by
  intro S K
  funext a b
  apply actual
  intro q r
  simp only [NumberedWindowArithmeticAnnotationProof.term]
  change ((! (encodeTerm q == encodeTerm (.bottom q.type))) &&
    (encodeTerm (.bottom q.type) == encodeTerm r)) = _
  rw [NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.1,
      NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.1]
  rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootProof
