module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationExchangeProof
open NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicApplicationTableProof (rowAt auxView rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAtomicLeastChecks (exact_AtomicExchangeRows)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (row table termNext bits parts)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowScalarAlgorithm (edge)

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

theorem rawExchange : ExactAtomicAuxExchange := by
  intro hp dom cod fn arg q atom hSyntax
  constructor
  · intro h
    obtain ⟨fs,hpOut⟩ := tagsFromSource hp dom cod fn arg q h
    obtain ⟨dom',cod',fn',a,code⟩ := exactTag6 hpOut hSyntax
    subst q
    rw [rowAuxPair,(atomRows hp atom fn').1] at h
    have same : (dom = dom' ∧ cod = cod') ∧ fn = fn' ∧ (row hp arg a).1 = true := by
      simpa only [Bool.false_and,Bool.false_or,Bool.and_eq_true,beq_iff_eq] using h
    exact ⟨a,by rw [same.1.1,same.1.2,same.2.1],same.2.2⟩
  · intro h
    obtain ⟨fs,hpIn⟩ := tagsFromTarget hp dom cod fn arg q h
    obtain ⟨dom',cod',fn',a,code⟩ := exactTag6 hpIn hSyntax
    subst q
    rw [rowAuxPair,(atomRows hp atom fn').2] at h
    have same : (dom' = dom ∧ cod' = cod) ∧ fn' = fn ∧ (row hp a arg).1 = true := by
      simpa only [Bool.false_and,Bool.false_or,Bool.and_eq_true,beq_iff_eq] using h
    exact ⟨a,by rw [same.1.1,same.1.2,same.2.1],same.2.2⟩

theorem scalarExchange : ExactAtomicAuxScalarEdges := by
  intro s Γ requested dom cod fn arg q atom
  constructor
  · intro h
    simp only [edge,bits,Bool.and_eq_true,and_assoc] at h
    obtain ⟨_,syn,raw,_,present⟩ := h
    obtain ⟨a,same,step⟩ := (rawExchange s.equivalentHeads dom cod fn arg q atom syn).1 raw
    exact ⟨a,same,step,present⟩
  · intro h
    simp only [edge,bits,Bool.and_eq_true,and_assoc] at h
    obtain ⟨syn,_,raw,present,_⟩ := h
    obtain ⟨a,same,step⟩ := (rawExchange s.equivalentHeads dom cod fn arg q atom syn).2 raw
    exact ⟨a,same,step,present⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationExchangeProof
