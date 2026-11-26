module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExchangeSpineRankProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (bits row termNext parts)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank tableEarlier)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView rowAt rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowRawExchangeVerticesCodecProof (getFieldLt)

private theorem syntaxLength (n : Nat) : (NumberedWindowSyntaxAlgorithm.table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [NumberedWindowSyntaxAlgorithm.table,ih]

private theorem syntaxEarlier {i n : Nat} (h : i < n) :
    (NumberedWindowSyntaxAlgorithm.table n).getD i (false,false) = syntaxBits i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : i < n
    · have short : i < (NumberedWindowSyntaxAlgorithm.table n).length := by simpa only [syntaxLength] using prior
      rw [List.getD_eq_getElem?_getD,NumberedWindowSyntaxAlgorithm.table,List.getElem?_append_left short,
        ← List.getD_eq_getElem?_getD]
      exact ih prior
    · have last : i = n := by omega
      subst i
      rw [List.getD_eq_getElem?_getD,NumberedWindowSyntaxAlgorithm.table,
        List.getElem?_append_right (by rw [syntaxLength]; exact Nat.le_refl n),syntaxLength,Nat.sub_self]
      rfl

private theorem exactFields (q : Nat) (fs : List Nat)
    (valid : (syntaxBits q).1 = true) (h : unpackNode q = some (6,fs)) :
    ∃ d c f a, fs = [d,c,f,a] ∧ q = auxRaw d c f a := by
  simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,h,Option.any_some] at valid
  rcases fs with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨a,_ | ⟨x,xs⟩⟩⟩⟩⟩ <;>
    simp [NumberedWindowSyntaxAlgorithm.termParts] at valid
  exact ⟨d,c,f,a,rfl,codeOfNode h⟩

private theorem syntaxChild (q d c f a : Nat)
    (view : unpackNode q = some (6,[d,c,f,a])) (valid : (syntaxBits q).1 = true) :
    (syntaxBits f).1 = true := by
  have small : f < q := getFieldLt view 2
  simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,view,Option.any_some,
    NumberedWindowSyntaxAlgorithm.termParts,Bool.and_eq_true] at valid
  have known := valid.1.2
  rw [syntaxEarlier small] at known
  exact known

theorem exact_RawRankAux (q d c f a : Nat)
    (view : unpackNode q = some (6,[d,c,f,a])) :
    rawRank q = (if rawRank f = 0 then 0 else rawRank f+1) := by
  have small : f < q := getFieldLt view 2
  unfold rawRank at *
  change NumberedWindowNeutralSpineRankAlgorithm.next q (NumberedWindowNeutralSpineRankAlgorithm.table q) = _
  rw [NumberedWindowNeutralSpineRankAlgorithm.next,view]
  change (if (NumberedWindowNeutralSpineRankAlgorithm.table q).getD f 0 = 0 then 0 else
    (NumberedWindowNeutralSpineRankAlgorithm.table q).getD f 0 + 1) = _
  rw [tableEarlier f q small] <;> rfl

private theorem bothTags (hp : HeadPairs) (a b : Nat) (held : (row hp a b).1 = true) :
    ∃ tag fs gs, unpackNode a = some (tag,fs) ∧ unpackNode b = some (tag,gs) ∧
      parts hp (NumberedWindowExchangeAlgorithm.table hp (NumberedWindowPairAlgorithm.pair a b))
        tag tag fs gs = true := by
  rw [rowAt] at held
  unfold termNext at held
  cases ha : unpackNode a with
  | none => simp [ha] at held
  | some qa =>
    cases hb : unpackNode b with
    | none => simp [ha,hb] at held
    | some qb =>
      obtain ⟨i,fs⟩ := qa
      obtain ⟨j,gs⟩ := qb
      have yes : parts hp (NumberedWindowExchangeAlgorithm.table hp (NumberedWindowPairAlgorithm.pair a b))
          i j fs gs = true := by simpa [ha,hb] using held
      by_cases same : i = j
      · subst j
        exact ⟨i,fs,gs,rfl,rfl,yes⟩
      · simp [parts,same] at yes

private theorem rankOfOther (q tag : Nat) (fs : List Nat)
    (read : unpackNode q = some (tag,fs)) (zero : tag ≠ 0) (bottom : tag ≠ 3) (aux : tag ≠ 6) :
    rawRank q = 0 := by
  simp [rawRank,NumberedWindowNeutralSpineRankAlgorithm.next,read,
    NumberedWindowNeutralSpineRankAlgorithm.row,zero,bottom,aux]

private theorem rankAtSum (hp : HeadPairs) : ∀ n a b : Nat, a+b = n →
    (bits hp a b).1 = true → rawRank a = rawRank b := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b sum held
    simp only [bits,Bool.and_eq_true] at held
    obtain ⟨tag,fs,gs,ha,hb,branch⟩ := bothTags hp a b held.2
    by_cases aux : tag = 6
    · subst tag
      obtain ⟨d,c,f,u,rfl,ae⟩ := exactFields a fs held.1.1 ha
      obtain ⟨d',c',f',u',rfl,be⟩ := exactFields b gs held.1.2 hb
      have rr := held.2
      rw [ae,be,rowAuxPair] at rr
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at rr
      have fnRank : rawRank f = rawRank f' := by
        rcases rr.2 with fn | arg
        · have smaller : f + f' < n := by
            have left : f < a := getFieldLt ha 2
            have right : f' < b := getFieldLt hb 2
            omega
          apply ih (f + f') smaller f f' rfl
          simp only [bits,Bool.and_eq_true]
          exact ⟨⟨syntaxChild a d c f u ha held.1.1,syntaxChild b d' c' f' u' hb held.1.2⟩,fn.1⟩
        · rw [arg.1]
      rw [exact_RawRankAux a d c f u ha,exact_RawRankAux b d' c' f' u' hb,fnRank]
    · have zero : tag ≠ 0 := by
        intro h
        subst tag
        simp [parts] at branch
      have bottom : tag ≠ 3 := by
        intro h
        subst tag
        simp [parts] at branch
      rw [rankOfOther a tag fs ha zero bottom aux,rankOfOther b tag gs hb zero bottom aux]

/-- Original directed term exchange preserves the raw neutral-spine
rank, without a packed-window, cover, or head-symmetry premise. -/
theorem exact_LiteralExchangeSpineRank (hp : HeadPairs) (a b : Nat)
    (held : (bits hp a b).1 = true) : rawRank a = rawRank b :=
  rankAtSum hp (a+b) a b rfl held

#print axioms exact_RawRankAux
#print axioms exact_LiteralExchangeSpineRank
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExchangeSpineRankProof
