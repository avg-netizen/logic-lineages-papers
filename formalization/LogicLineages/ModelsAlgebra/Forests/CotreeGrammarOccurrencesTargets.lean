module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.Targets
open ForestParseRepresentationBinary CotreeGrammarShape

def WordMembership : Prop :=
  ∀ (I : Type) (s : Shape I) i, i ∈ word s ↔ ∃ p : Positions s, label s p = i

def WordNodup : Prop :=
  ∀ (I : Type) (s : Shape I), (word s).Nodup ↔ Function.Injective (label s)

def OccurrencePermutation : Prop :=
  ∀ n (s : Shape (Fin n)), (word s).Perm (List.finRange n) ↔ Function.Bijective (label s)

/-- A type-word permutation can be assigned to distinct actual child occurrences,
retaining the exact binary shape rather than merely its graph or multiset. -/
def TypeWordReindex : Prop :=
  ∀ (I A : Type) (n : Nat) (types : I → A) (children : Fin n → A) (s : Shape I),
    ((word s).map types).Perm (List.ofFn children) →
    ∃ r : Shape (Fin n), Paired (fun i j => types i = children j) s r ∧
      Function.Bijective (label r)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.Targets
