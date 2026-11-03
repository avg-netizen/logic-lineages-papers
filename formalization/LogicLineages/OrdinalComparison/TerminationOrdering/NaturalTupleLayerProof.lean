module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerProof
open Source Source.SourceArrowSuffixes Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer

theorem suffixCalibration : NaturalTupleLayerTargets.SuffixCalibration := by
  intro τ s
  obtain ⟨hn,he⟩ := (Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ s.val.1 s.val.2).mp s.property
  have hs := Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ s.val.1 s.val.2 s.property
  exact ⟨hn,he,hs.1,fun i => hs.2 _ (List.get_mem _ _)⟩

theorem exhaustiveEnumeration : NaturalTupleLayerTargets.ExhaustiveEnumeration := by
  intro Symbol inst arity I τ D P a
  exact Finset.mem_univ a

theorem weakeningIdentity : NaturalTupleLayerTargets.WeakeningIdentity := by
  intro Symbol arity I τ D P a
  rfl

theorem weakeningComposition : NaturalTupleLayerTargets.WeakeningComposition := by
  intro Symbol arity I τ D P Q R h k a
  rfl

theorem naturalPreservation : NaturalTupleLayerTargets.NaturalPreservation := by
  intro Symbol arity I τ D P Q h a ha
  constructor
  · intro R s v w hv
    exact ha.1 ⟨R.val,fun p hp => R.property p (h p hp)⟩ s v w hv
  · intro R T k s v
    exact ha.2 ⟨R.val,fun p hp => R.property p (h p hp)⟩
      ⟨T.val,fun p hp => T.property p (h p hp)⟩ k s v

theorem weakeningMonotone : NaturalTupleLayerTargets.WeakeningMonotone := by
  intro Symbol arity I τ D P Q h a b hab
  constructor
  · intro R
    exact hab.1 ⟨R.val,fun p hp => R.property p (h p hp)⟩
  · intro R s v
    exact hab.2 ⟨R.val,fun p hp => R.property p (h p hp)⟩ s v

/-- Finite pointwise order decisions, with no arbitrary-predicate choice. -/
instance finiteFunctionOrderDecision {α : Type} [Fintype α] {β : α → Type}
    [∀ i,LE (β i)] [∀ i,DecidableRel (fun a b : β i => a ≤ b)]
    (f g : (i : α) → β i) : Decidable (f ≤ g) :=
  inferInstanceAs (Decidable (∀ i,f i ≤ g i))

/-- The generic construction outputs the same computational ordered-family interface.
No completeness/lattice oracle is added; later recursion supplies every lower family. -/
def layerFamily {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) : Family I where
  carrier := Natural I τ D
  finite := fun P => naturalFinite I τ D P
  equality := fun P a b =>
    decidable_of_iff (a.val ≤ b.val ∧ b.val ≤ a.val)
      ⟨fun h => Subtype.ext (le_antisymm h.1 h.2),fun h => by cases h; exact ⟨le_rfl,le_rfl⟩⟩
  order := fun P => inferInstance
  orderDecision := fun P a b => by
    change Decidable (a.val ≤ b.val)
    infer_instance
  restrict := fun {P Q} h a => ⟨rawWeaken h a.val,naturalPreservation Symbol arity I τ D P Q h a.val a.property⟩
  restrictIdentity := by
    intro P a
    apply Subtype.ext
    exact weakeningIdentity Symbol arity I τ D P a.val
  restrictComposition := by
    intro P Q R h k a
    apply Subtype.ext
    exact weakeningComposition Symbol arity I τ D P Q R h k a.val
  restrictMonotone := by
    intro P Q h a b hab
    exact weakeningMonotone Symbol arity I τ D P Q h a.val b.val hab

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerProof
