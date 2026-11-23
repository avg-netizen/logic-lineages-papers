module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpinePositiveRankProof
import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
open NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicApplicationTableProof (rowAt auxView rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAtomicLeastChecks (exact_AtomicExchangeRows)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (row table termNext bits parts)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowAuxExchangeLiftChecks (exact_AuxTermSyntax)
open NumberedWindowNeutralSpineRawRankProof (NeutralSpineRank)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankCalibrationProof (exact_OriginalRawNeutralRankIff)
open NumberedWindowNeutralSpinePositiveRankProof (KeepsNeutralRank)

private theorem atomRows (hp : HeadPairs) {fn : Nat} (a : AtomHead fn) (q : Nat) :
    (row hp fn q).1 = false ∧ (row hp q fn).1 = false := by
  constructor
  · rw [rowAt]
    cases a with
    | free t n => exact (exact_AtomicExchangeRows.1 hp (table hp (pair _ q)) t n q).1
    | bottom t => exact (exact_AtomicExchangeRows.2 hp (table hp (pair _ q)) t q).1
  · rw [rowAt]
    cases a with
    | free t n => exact (exact_AtomicExchangeRows.1 hp (table hp (pair q _)) t n q).2
    | bottom t => exact (exact_AtomicExchangeRows.2 hp (table hp (pair q _)) t q).2

private theorem exactTag6 {q : Nat} {fs : List Nat}
    (seen : unpackNode q = some (6,fs)) (ok : (syntaxBits q).1 = true) :
    ∃ s t f a, q = auxRaw s t f a := by
  simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,seen,Option.any_some] at ok
  rcases fs with _ | ⟨s,_ | ⟨t,_ | ⟨f,_ | ⟨a,_ | ⟨b,rest⟩⟩⟩⟩⟩ <;>
    simp [NumberedWindowSyntaxAlgorithm.termParts] at ok
  exact ⟨s,t,f,a,codeOfNode seen⟩

private theorem tagsFromSource (hp : HeadPairs) (dom cod fn arg q : Nat)
    (h : (row hp (auxRaw dom cod fn arg) q).1 = true) :
    ∃ fs, unpackNode q = some (6,fs) := by
  rw [rowAt,termNext,auxView] at h
  cases hq : unpackNode q with
  | none => simp [hq] at h
  | some node =>
    rcases node with ⟨tag,fs⟩
    by_cases same : tag = 6
    · subst tag
      exact ⟨fs,by first | exact hq | rfl⟩
    · have diff : 6 ≠ tag := Ne.symm same
      simp [hq,parts,diff] at h

private theorem tagsFromTarget (hp : HeadPairs) (dom cod fn arg q : Nat)
    (h : (row hp q (auxRaw dom cod fn arg)).1 = true) :
    ∃ fs, unpackNode q = some (6,fs) := by
  rw [rowAt,termNext,auxView] at h
  cases hq : unpackNode q with
  | none => simp [hq] at h
  | some node =>
    rcases node with ⟨tag,fs⟩
    by_cases same : tag = 6
    · subst tag
      exact ⟨fs,by first | exact hq | rfl⟩
    · simp [hq,parts,same] at h


private theorem childSyntax (d c f a : Nat) (h : (syntaxBits (auxRaw d c f a)).1 = true) :
    (syntaxBits f).1 = true := by
  rw [exact_AuxTermSyntax d c f a] at h
  simp only [Bool.and_eq_true,and_assoc] at h
  exact h.2.2.1

/-- Both directions of the real directed bit preserve a present neutral
shape and the same rank. The orientations are proved together, not by
assuming the exchange relation is symmetric. -/
theorem exact_OriginalNeutralSpineExchange (hp : HeadPairs) {q rank : Nat}
    (shape : NeutralSpineRank q rank) :
    ∀ p, ((bits hp q p).1 = true → NeutralSpineRank p rank) ∧
      ((bits hp p q).1 = true → NeutralSpineRank p rank) := by
  induction shape with
  | free stored name =>
    intro p
    have none := atomRows hp (AtomHead.free stored name) p
    exact ⟨by simp [bits,none.1],by simp [bits,none.2]⟩
  | bottom stored =>
    intro p
    have none := atomRows hp (AtomHead.bottom stored) p
    exact ⟨by simp [bits,none.1],by simp [bits,none.2]⟩
  | @aux fn rank dom cod arg fnShape ih =>
    intro p
    constructor
    · intro accepted
      simp only [bits,Bool.and_eq_true,and_assoc] at accepted
      obtain ⟨sx,sy,test⟩ := accepted
      obtain ⟨fs,targetTag⟩ := tagsFromSource hp dom cod fn arg p test
      obtain ⟨dom',cod',fn',arg',packed⟩ := exactTag6 targetTag sy
      subst p
      rw [rowAuxPair] at test
      have two : ((row hp fn fn').1 = true ∧ arg = arg') ∨
          (fn = fn' ∧ (row hp arg arg').1 = true) := by
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] at test
        exact test.2.2
      rcases two with ⟨call,_⟩ | ⟨same,_⟩
      · have inner : (bits hp fn fn').1 = true := by
          simp [bits,childSyntax dom cod fn arg sx,childSyntax dom' cod' fn' arg' sy,call]
        exact .aux dom' cod' arg' ((ih fn').1 inner)
      · subst fn'
        exact .aux dom' cod' arg' fnShape
    · intro accepted
      simp only [bits,Bool.and_eq_true,and_assoc] at accepted
      obtain ⟨sx,sy,test⟩ := accepted
      obtain ⟨fs,sourceTag⟩ := tagsFromTarget hp dom cod fn arg p test
      obtain ⟨dom',cod',fn',arg',packed⟩ := exactTag6 sourceTag sx
      subst p
      rw [rowAuxPair] at test
      have two : ((row hp fn' fn).1 = true ∧ arg' = arg) ∨
          (fn' = fn ∧ (row hp arg' arg).1 = true) := by
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] at test
        exact test.2.2
      rcases two with ⟨call,_⟩ | ⟨same,_⟩
      · have inner : (bits hp fn' fn).1 = true := by
          simp [bits,childSyntax dom' cod' fn' arg' sx,childSyntax dom cod fn arg sy,call]
        exact .aux dom' cod' arg' ((ih fn').2 inner)
      · subst fn'
        exact .aux dom' cod' arg' fnShape

/-- This equality also covers the absence of a neutral shape, by
inverting a hypothetical positive rank through the reverse orientation. -/
theorem exact_OriginalNeutralSpineBitsRank (hp : HeadPairs) (a b : Nat)
    (accepted : (bits hp a b).1 = true) : rawRank b = rawRank a := by
  cases ha : rawRank a with
  | zero =>
    cases hb : rawRank b with
    | zero => rfl
    | succ n =>
      have shape := (exact_OriginalRawNeutralRankIff b n).mp hb
      have target := (exact_OriginalNeutralSpineExchange hp shape a).2 accepted
      have absurd := (exact_OriginalRawNeutralRankIff a n).mpr target
      rw [ha] at absurd
      cases absurd
  | succ n =>
    have shape := (exact_OriginalRawNeutralRankIff a n).mp ha
    exact (exact_OriginalRawNeutralRankIff b n).mpr
      ((exact_OriginalNeutralSpineExchange hp shape b).1 accepted)

theorem exact_OriginalKeepsNeutralRank (s : Settings) : KeepsNeutralRank s := by
  intro ctx ty a b accepted
  simp only [edge,Bool.and_eq_true,and_assoc] at accepted
  exact exact_OriginalNeutralSpineBitsRank s.equivalentHeads a b accepted.1

#print axioms exact_OriginalNeutralSpineExchange
#print axioms exact_OriginalKeepsNeutralRank
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
