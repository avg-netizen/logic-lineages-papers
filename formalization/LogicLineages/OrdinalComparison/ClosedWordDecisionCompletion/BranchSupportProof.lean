module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordFormulaProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.SupportProof
public import Mathlib.Data.Finset.Card

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LogicLineages.ModelsAlgebra.Forests

/-- Actual raw-name containment with one occurring name absent is a strict
finite cardinal decrease. Repeated occurrences and coefficient zero remain. -/
theorem strict_name_decrease (p q : Formula) (x : Nat) (hx : x ∈ names p)
    (hq : ∀ i ∈ q.variables, i ≠ x ∧ i ∈ p.variables) :
    (names q).length < (names p).length := by
  have hs : q.variables.toFinset ⊆ p.variables.toFinset.erase x := by
    intro i hi
    have hh := hq i (List.mem_toFinset.mp hi)
    exact Finset.mem_erase.mpr ⟨hh.1,List.mem_toFinset.mpr hh.2⟩
  have hm : x ∈ p.variables.toFinset :=
    List.mem_toFinset.mpr (List.mem_dedup.mp hx)
  calc
    (names q).length = q.variables.toFinset.card := (List.card_toFinset q.variables).symm
    _ ≤ (p.variables.toFinset.erase x).card := Finset.card_le_card hs
    _ < p.variables.toFinset.card := Finset.card_erase_lt_of_mem hm
    _ = (names p).length := List.card_toFinset p.variables

theorem specialized_names (x n : Nat) (p : Formula) (i : Nat) :
    i ∈ (OriginalWordEvaluation.specialize x n p).variables ↔
      i ≠ x ∧ i ∈ p.variables := by
  simp only [Formula.variables]
  rw [OriginalWordEvaluation.Proof.exactSupport x n p]
  simp only [List.mem_map]
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hx⟩ := List.mem_filter.mp ht
    exact ⟨by simpa using hx,⟨t,ht,rfl⟩⟩
  · rintro ⟨hx,t,ht,rfl⟩
    exact ⟨t,List.mem_filter.mpr ⟨ht,by simpa using hx⟩,rfl⟩

theorem specialized_allowed (D x n : Nat) (p : Formula) (hp : Formula.allowed D p) :
    Formula.allowed D (OriginalWordEvaluation.specialize x n p) := by
  intro t ht
  rw [OriginalWordEvaluation.Proof.exactSupport] at ht
  exact hp t (List.mem_filter.mp ht).1

theorem prefix_child_syntax (D floor N : Nat) (p : Formula)
    (hp : Formula.allowed D p) (b : Branch) (hb : b ∈ prefixChildren floor N p) :
    b.1 = floor ∧ Formula.allowed D b.2 ∧
    (∃ x ∈ names p, ∀ i ∈ b.2.variables, i ≠ x ∧ i ∈ p.variables) ∧
    (names b.2).length < (names p).length := by
  obtain ⟨x,hx,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨k,hk,he⟩ := List.mem_filterMap.mp hb
  dsimp only at he
  split at he
  next hdom =>
    have he' : (floor,OriginalWordEvaluation.specialize x (floor+k) p) = b :=
      Option.some.inj he
    subst b
    have hs : ∀ i ∈ (OriginalWordEvaluation.specialize x (floor+k) p).variables,
        i ≠ x ∧ i ∈ p.variables :=
      fun i hi => (specialized_names x (floor+k) p i).mp hi
    exact ⟨rfl,specialized_allowed D x (floor+k) p hp,
      ⟨x,hx,hs⟩,strict_name_decrease p _ x hx hs⟩
  next hdom => contradiction

theorem frame_tokens (N maximum : Nat) (ns : List Nat) :
    (frame N maximum ns).tokens =
      ns.flatMap (fun i => [(i,[]),(maximum,[]),(i,[])]) := by
  induction ns with
  | nil => rfl
  | cons i ns ih =>
      simp only [frame,List.foldr_cons,Formula.tokens,CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_cons,List.flatMap_nil,List.flatMap_append,List.append_nil,
        Atom.row,lowerRow,maximumRow,List.map_cons,List.map_nil,List.cons_append]
      exact congrArg (fun ts => (i,[])::(maximum,[])::(i,[])::ts) ih

theorem frame_word_empty (N maximum : Nat) (ns : List Nat) (t : Token)
    (ht : t ∈ (frame N maximum ns).tokens) : t.2 = [] := by
  rw [frame_tokens] at ht
  obtain ⟨i,hi,ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

theorem frame_allowed (D N maximum : Nat) (ns : List Nat) :
    Formula.allowed D (frame N maximum ns) := by
  intro t ht a ha
  rw [frame_word_empty N maximum ns t ht] at ha
  contradiction

theorem frame_meaningful (N maximum : Nat) (ns : List Nat) (ν : Nat → Nat) :
    Formula.meaningful (frame N maximum ns) ν := by
  intro t ht
  rw [frame_word_empty N maximum ns t ht]
  trivial

theorem frame_linear (N maximum x : Nat) (ns : List Nat) :
    linear x (frame N maximum ns) = true := by
  rw [linear,List.all_eq_true]
  intro t ht
  simp [frame_word_empty N maximum ns t ht]

theorem frame_names (N maximum : Nat) (ns : List Nat) (hmax : maximum ∈ ns) :
    FormulaNamesFrom ns (frame N maximum ns) := by
  intro i hi
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
  rw [frame_tokens] at ht
  obtain ⟨j,hj,ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact hj
  · exact hmax
  · exact hj

theorem lowerRow_value (N i : Nat) (ν : Nat → Nat) :
    RowValue (lowerRow N i) ν = (ν i : Int)-(N : Int) := by
  simp [lowerRow,RowValue,wordValue] <;> omega

theorem maximumRow_value (maximum i : Nat) (ν : Nat → Nat) :
    RowValue (maximumRow maximum i) ν = (ν maximum : Int)-(ν i : Int) := by
  simp [maximumRow,RowValue,wordValue] <;> omega

theorem frame_eval (N maximum : Nat) (ns : List Nat) (ν : Nat → Nat) :
    Formula.eval ν (frame N maximum ns) ↔
      ∀ i ∈ ns, N ≤ ν i ∧ ν i ≤ ν maximum := by
  induction ns with
  | nil => simp [frame,Formula.eval]
  | cons i ns ih =>
      have hlo : 0 ≤ (ν i : Int)-(N : Int) ↔ N ≤ ν i := by omega
      have hhi : 0 ≤ (ν maximum : Int)-(ν i : Int) ↔ ν i ≤ ν maximum := by omega
      simpa only [frame,List.foldr_cons,Formula.eval,Atom.eval,lowerRow_value,
        maximumRow_value,hlo,hhi,List.forall_mem_cons,and_assoc] using
        and_congr (Iff.rfl : (N ≤ ν i) ↔ N ≤ ν i)
          (and_congr (Iff.rfl : (ν i ≤ ν maximum) ↔ ν i ≤ ν maximum) ih)

#print axioms strict_name_decrease
#print axioms specialized_names
#print axioms specialized_allowed
#print axioms prefix_child_syntax
#print axioms frame_tokens
#print axioms frame_word_empty
#print axioms frame_allowed
#print axioms frame_meaningful
#print axioms frame_linear
#print axioms frame_names
#print axioms lowerRow_value
#print axioms maximumRow_value
#print axioms frame_eval

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
