module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBodyWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowRawContextOwnFuelProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedChildNumericProof
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowInternalSparsePathAdvanceTargets (packedRaw)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowRawContextAlgorithm (next context raw run tick iterate windowStep Frame RawRoot)
open NumberedWindowRawContextOwnFuelProof (exact_RawContextOwnHop exact_ContextWitnessDescends)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowFieldAlgorithm (unpackNode unpack pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)
open NumberedWindowInternalLiteralLambdaBodyWindowNumericProof (exact_LiteralOriginalLambdaBothBodyWindows)

private theorem acceptedNext (P : RawRoot) (q w r child : Nat)
    (witness : unpackNode w = some (1,[child]))
    (accepted : run P w q w r = true) :
    ∃ (target : Frame), next 1 [child] q r = some target := by
  cases n : next 1 [child] q r with
  | some target => exact ⟨target,rfl⟩
  | none =>
    have wpos := (nodeBounds witness).1
    cases w with
    | zero => omega
    | succ f =>
      have past : ∀ k, iterate P k (false,none) = (false,none) := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => simp [iterate,tick,ih]
      change (iterate P f (tick P (false,some (q,f+1,r)))).1 = true at accepted
      simp [tick,witness,n,past] at accepted

private theorem literalBodies (q r child a c b : Nat)
    (n : next 1 [child] q r = some (a,c,b)) :
    c = child ∧ ∃ d, unpackNode q = some (2,[d,a]) ∧ unpackNode r = some (2,[d,b]) := by
  unfold next at n
  cases l : unpackNode q with
  | none => simp [l] at n
  | some left =>
    cases rr : unpackNode r with
    | none => simp [l,rr] at n
    | some right =>
      simp only [l,rr,Option.bind_eq_bind,Option.bind_some] at n
      unfold context at n
      split at n
      case h_1 =>
        split at n <;> simp_all
      all_goals simp_all

private theorem syntaxOfAdmitted (s : Settings) (ctx : List Nat) (ty raw : Nat)
    (valid : admitted s ctx ty raw = true) : (syntaxBits raw).1 = true := by
  simp only [admitted,typed,Bool.and_eq_true] at valid
  exact valid.1.1.1

/-- Every successful original numeral raw step using the lambda frame
has the actual body step at the pushed original lexical context and
its own smaller certificate. This applies repeatedly down leading
lambda frames, with no assumption of a closed body or bound context. -/
theorem exact_OriginalNumericLambdaTypedChild (xs : Entries) (s : Settings)
    (ctx ty q w r child : Nat) (witness : unpackNode w = some (1,[child]))
    (accepted : packedRaw xs s ctx ty q w r = true) :
    ∃ d cod a b, unpackNode q = some (2,[d,a]) ∧ unpackNode r = some (2,[d,b]) ∧
      ty = arrow d cod ∧ child < w ∧
      packedWindow s (pair d ctx + 1) cod a = true ∧
      packedWindow s (pair d ctx + 1) cod b = true ∧
      packedRaw xs s (pair d ctx + 1) cod a child b = true := by
  let P := root xs s
  cases gk : unpack ctx with
  | none => simp [packedRaw,gk] at accepted
  | some g =>
    simp only [packedRaw,gk,Option.any_some,step,windowStep,raw,Bool.and_eq_true] at accepted
    obtain ⟨⟨⟨⟨_,_⟩,runOk⟩,qTyped⟩,rTyped⟩ := accepted
    obtain ⟨⟨a,k,b⟩,moved⟩ := acceptedNext P q w r child witness runOk
    obtain ⟨rfl,d,left,right⟩ := literalBodies q r child a k b moved
    have wq : packedWindow s ctx ty q = true := by simpa only [packedWindow,gk,Option.any_some] using qTyped
    have wr : packedWindow s ctx ty r = true := by simpa only [packedWindow,gk,Option.any_some] using rTyped
    obtain ⟨cod,formula,old,new⟩ := exact_LiteralOriginalLambdaBothBodyWindows s ctx ty q r d a b left right wq wr
    have smaller := exact_ContextWitnessDescends witness moved
    have ran := (exact_RawContextOwnHop P (by decide : (1 : Nat) ≠ 0) witness moved).symm.trans runOk
    have repack : pair d ctx + 1 = pack (d :: g) := by rw [packOfUnpack ctx gk]; rfl
    have read : unpack (pair d ctx + 1) = some (d :: g) := by rw [repack]; exact unpackPacked (d :: g)
    have aw : admitted s (d :: g) cod a = true := by simpa only [packedWindow,read,Option.any_some] using old
    have bw : admitted s (d :: g) cod b = true := by simpa only [packedWindow,read,Option.any_some] using new
    refine ⟨d,cod,a,b,left,right,formula,smaller,old,new,?_⟩
    simp only [packedRaw,read,Option.any_some,step,windowStep,raw,Bool.and_eq_true]
    exact ⟨⟨⟨⟨syntaxOfAdmitted s (d :: g) cod a aw,syntaxOfAdmitted s (d :: g) cod b bw⟩,ran⟩,aw⟩,bw⟩

#print axioms exact_OriginalNumericLambdaTypedChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedChildNumericProof
