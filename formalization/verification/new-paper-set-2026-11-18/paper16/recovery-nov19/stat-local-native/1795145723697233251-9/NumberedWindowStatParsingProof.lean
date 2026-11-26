import LogicLineages.PersistentMarking.NumberedWindowStatTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowStatParsingProof
open NumberedWindowStatAlgorithm NumberedWindowStatTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticRawRootCode NumberedWindowArithmeticWitnessListCode
open NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticSyntaxAlgorithmChecks NumberedWindowArithmeticSyntaxAlgorithmTargets

theorem argsExact : ExactArgsView := by
  intro n
  unfold argsView
  rw [exact_ExactTermArgsGuards n]
  cases h : decodeArgs n with
  | none => simp [OriginalRow,h]
  | some qs =>
    have hn := (exact_ArgsCodec.1 n qs).mp h
    have hu := NumberedWindowArithmeticExchangeAtomsChecks.exact_EncodedArguments qs
    rw [hn] at hu
    simp [OriginalRow,h,hu]

private theorem syntaxTerm (n : Nat) :
    (NumberedWindowSyntaxAlgorithm.syntaxBits n).1 = (decodeTerm n).isSome := by
  rw [exact_ExactTermArgsGuards n]
  rfl

private theorem elements (codes : List Nat) :
    (if codes.all (fun c => (NumberedWindowSyntaxAlgorithm.syntaxBits c).1) then some codes else none) =
      (decodeElements decodeTerm codes).map (List.map encodeTerm) := by
  induction codes with
  | nil => rfl
  | cons c cs ih =>
    cases hc : decodeTerm c with
    | none => simp [syntaxTerm,hc,decodeElements]
    | some q =>
      have he := (exact_TermCodec.1 c q).mp hc
      cases ht : decodeElements decodeTerm cs with
      | none =>
        have hg : (cs.all (fun c => (NumberedWindowSyntaxAlgorithm.syntaxBits c).1)) = false := by
          cases hg : cs.all (fun c => (NumberedWindowSyntaxAlgorithm.syntaxBits c).1)
          · rfl
          · simp [hg,ht] at ih
        simp [List.all_cons,syntaxTerm c,hc,ht,decodeElements,hg]
      | some qs =>
        have hg : (cs.all (fun c => (NumberedWindowSyntaxAlgorithm.syntaxBits c).1)) = true := by
          cases hg : cs.all (fun c => (NumberedWindowSyntaxAlgorithm.syntaxBits c).1)
          · simp [hg,ht] at ih
          · rfl
        have hcs : cs = qs.map encodeTerm := by simpa [hg,ht] using ih
        simp [List.all_cons,syntaxTerm c,hc,ht,decodeElements,hg,he,hcs]

theorem termCodesExact (n : Nat) :
    termCodes n = (decodeTermList n).map (List.map encodeTerm) := by
  unfold termCodes decodeTermList decodeListOf
  rw [← exact_ExactOrderedFieldCodec.2]
  cases NumberedWindowArithmeticFields.decodeFields n with
  | none => rfl
  | some cs => simpa only [Option.bind_eq_bind,Option.bind_some] using elements cs

theorem partitionExact : ExactPartitionView := by
  intro n
  unfold readPartition decodeReplacement
  rw [← exact_ExactTaggedNodeCodec.2]
  cases hn : NumberedWindowArithmeticFields.decodeNode n with
  | none => rfl
  | some x =>
    rcases x with ⟨tag,fs⟩
    rcases tag with _ | tag <;>
      rcases fs with _ | ⟨k,_ | ⟨r,_ | ⟨a,_ | ⟨x,xs⟩⟩⟩⟩
    all_goals try rfl
    change (do
      let ks ← termCodes k
      let rs ← termCodes r
      let as ← termCodes a
      pure (ks,rs,as)) = _
    rw [termCodesExact,termCodesExact,termCodesExact]
    cases decodeTermList k <;> cases decodeTermList r <;> cases decodeTermList a <;>
      rfl

end LogicLineages.PersistentMarking.NumberedWindowStatParsingProof
