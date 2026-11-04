module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetSupportProof
open PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators PositiveArithmeticLeastSet
open TaggedArithmeticOperatorsSupportProof

theorem unfolding (body : Positive (Fin 2)) (context x : Nat) :
    x ∈ leastSet body context ↔ realize (fun y => y ∈ leastSet body context) body.formula ![context,x] := by
  have h := (operator body context).map_lfp
  exact (congrArg (fun P : Set Nat => x ∈ P) h).symm.to_iff

theorem leastness (body : Positive (Fin 2)) (context : Nat) (P : Set Nat)
    (h : ∀ x, realize (fun y => y ∈ P) body.formula ![context,x] → x ∈ P) : leastSet body context ⊆ P :=
  (operator body context).lfp_le h

def joinTags (A B : Set Nat) : Set Nat :=
  {z | (∃ x, tagNumber false x=z ∧ x∈A) ∨ ∃ x, tagNumber true x=z ∧ x∈B}

theorem joinEven (A B : Set Nat) (x : Nat) : tagNumber false x ∈ joinTags A B ↔ x∈A := by
  constructor
  · rintro (⟨y,he,hy⟩ | ⟨y,he,hy⟩)
    · have h := tagInjective false he
      subst y
      exact hy
    · exact False.elim (tagsDisjoint x y he.symm)
  · intro h
    exact Or.inl ⟨x,rfl,h⟩

theorem joinOdd (A B : Set Nat) (x : Nat) : tagNumber true x ∈ joinTags A B ↔ x∈B := by
  constructor
  · rintro (⟨y,he,hy⟩ | ⟨y,he,hy⟩)
    · exact False.elim (tagsDisjoint y x he)
    · have h := tagInjective true he
      subst y
      exact hy
  · intro h
    exact Or.inr ⟨x,rfl,h⟩

theorem combinedBelowJoin (scalar multiset : Positive (Fin 2)) (context : Nat) :
    leastSet (combinedOperator scalar multiset) context ⊆
      joinTags (leastSet scalar context) (leastSet multiset context) := by
  apply leastness
  intro z hz
  obtain ⟨⟨odd,x⟩,he,_⟩ := TaggedArithmeticOperatorsProof.tagPartition z
  subst z
  cases odd
  · apply (joinEven _ _ x).mpr
    apply (unfolding scalar context x).mpr
    have h := (TaggedArithmeticOperatorsProof.taggedBranchIsolation scalar multiset
      (fun y => y∈joinTags (leastSet scalar context) (leastSet multiset context)) context x).1.mp hz
    have hp : (fun y => tagNumber false y ∈ joinTags (leastSet scalar context) (leastSet multiset context)) =
        (fun y => y∈leastSet scalar context) := by
      funext y
      exact propext (joinEven _ _ y)
    rw [hp] at h
    exact h
  · apply (joinOdd _ _ x).mpr
    apply (unfolding multiset context x).mpr
    have h := (TaggedArithmeticOperatorsProof.taggedBranchIsolation scalar multiset
      (fun y => y∈joinTags (leastSet scalar context) (leastSet multiset context)) context x).2.mp hz
    have hp : (fun y => tagNumber true y ∈ joinTags (leastSet scalar context) (leastSet multiset context)) =
        (fun y => y∈leastSet multiset context) := by
      funext y
      exact propext (joinOdd _ _ y)
    rw [hp] at h
    exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetSupportProof
