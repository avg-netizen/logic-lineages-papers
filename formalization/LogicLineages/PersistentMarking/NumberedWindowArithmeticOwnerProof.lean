import LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerProof
open NumberedWindowOwnerAlgorithm NumberedWindowArithmeticOwnerTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticFieldAlgorithmChecks

private theorem ownerCode (f k bs es σ) :
    owner (encodeHead f) k (encodeArgs bs) (encodeArgs es) (encodeTy σ) =
      encodeTerm (.numbered f σ k bs es) := by
  unfold owner encodeTerm
  rw [exact_ExactTaggedNodeCodec.1]

theorem copiesExact : ExactOwnerCopies := by
  intro f k bs es domains
  induction domains with
  | nil => rfl
  | cons σ rest ih =>
    change NumberedWindowPairAlgorithm.pair _ (copies _ _ _ _ _) + 1 =
      NumberedWindowArithmeticPair.pair _ (encodeArgs (ownerCopies _ _ _ _ _)) + 1
    rw [← NumberedWindowActualPairAlgorithmChecks.currentPair, ih, ownerCode]

theorem arrowExact : ExactArrowPrefix := by
  intro domains result
  induction domains with
  | nil => rfl
  | cons σ rest ih =>
    change NumberedWindowPairAlgorithm.pair _ (plan _ _).1 + 1 =
      NumberedWindowArithmeticPair.pair _ (encodeTy (Spine.ArrowPrefix rest result)) + 1
    rw [← NumberedWindowActualPairAlgorithmChecks.currentPair,ih]

theorem selectedExact : ExactSelectedApplications := by
  intro f k bs es domains result q h
  induction domains generalizing q with
  | nil => exact ⟨q,rfl,rfl,h⟩
  | cons σ rest ih =>
    let cod := Spine.ArrowPrefix rest result
    let a := NTerm.numbered f σ k bs es
    let fn := NTerm.auxApp σ cod q a
    obtain ⟨r,hApp,hCode,hType⟩ := ih fn rfl
    refine ⟨r,?_,?_,hType⟩
    · change applications q (.cons a _) = _
      simp only [applications,h,Spine.ArrowPrefix,NTerm.type,ite_true,a]
      exact hApp
    · change applyCopies _ _ _ _ (NumberedWindowFieldAlgorithm.packNode 6
        [encodeTy σ,(plan _ _).1,encodeTerm q,owner _ _ _ _ (encodeTy σ)]) (plan _ _).2 = _
      rw [arrowExact rest result,ownerCode,← exact_ExactTaggedNodeCodec.1]
      exact hCode
end LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerProof
