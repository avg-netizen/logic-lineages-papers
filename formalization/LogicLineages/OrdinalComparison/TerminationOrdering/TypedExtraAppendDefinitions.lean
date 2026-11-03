module
public import LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppend
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets

instance packedEquality {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I} :
    DecidableEq (Packed I P) := fun a b =>
  decidable_of_iff (PackedLE a b ∧ PackedLE b a)
    ⟨fun h => (TypedExtraDownsetsProof.packedOrder Symbol inferInstance arity I P).2.2 a b h.1 h.2,
      fun h => by cases h; exact ⟨(TypedExtraDownsetsProof.packedOrder Symbol inferInstance arity I P).1 a,
        (TypedExtraDownsetsProof.packedOrder Symbol inferInstance arity I P).1 a⟩⟩

/-- Downward closure of all old extras and every member of the supplied list. -/
def appendRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (E : Extras I P) (xs : List (Packed I P)) (τ : TypeIndex I) : Finset (Value I τ.val P) :=
  Finset.univ.filter fun b => b ∈ (E τ).val ∨ ∃ p ∈ xs,PackedLE ⟨τ,b⟩ p

/-- Actual typed order coverage; full tuple pointwise increase implies this relation. -/
def Dominated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (xs ys : List (Packed I P)) : Prop := ∀ p ∈ xs,∃ q ∈ ys,PackedLE p q

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppend
