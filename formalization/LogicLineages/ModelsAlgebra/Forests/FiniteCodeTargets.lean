module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeDefinitions

/-! Exact code/actual-order comparison and genuine primitive-recursive finite
operations. These targets do not include unbounded certificate search, a bound
on the first bad pair, Carter's decision procedure or positive JEP decisions. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open FiniteCode

def ForestCodeCodecFaithful : Prop := ∀ c : Code, decode (encode c) = some c

def ForestCodeValidation : Prop :=
  ∀ (c : Code), valid c = true ↔
    (∀ e ∈ c.2, e.1 < c.1 ∧ e.2 < c.1) ∧
      ∃ po : PartialOrder (Fin c.1), @IsOrderForest (Fin c.1) po ∧
        ∀ i j : Fin c.1, @LE.le _ po.toLE i j ↔ Rel c i.val j.val

def ForestCodeEnumeration : Prop :=
  (∀ n c, c ∈ allRelations n ↔ c.1 = n ∧ c.2.Sublist (allPairs n)) ∧
  (∀ N c, c ∈ hostCodes N ↔ c.1 ≤ N ∧ c.2.Sublist (allPairs c.1)) ∧
  ∀ F : FiniteOrderForest,
    ∃ c ∈ allRelations (Fintype.card F.Carrier),
      ∃ hc : valid c = true, Nonempty (F.Carrier ≃o (toForest c hc).Carrier)

def ForestMapWordEnumeration : Prop :=
  ∀ n m xs, xs ∈ mapWords n m ↔ xs.length = n ∧ ∀ a ∈ xs, a < m

def ForestMapTestCorrect : Prop :=
  ∀ (c d : Code) (hc : valid c = true) (hd : valid d = true) (xs : List ℕ),
    mapTest c d xs = true ↔
      xs.length = c.1 ∧ (∀ a ∈ xs, a < d.1) ∧
      ∃ e : (toForest c hc).Carrier ↪o (toForest d hd).Carrier,
        ∀ i : Fin c.1, (e i).val = xs.getD i.val 0

def ForestEmbeddingTestCorrect : Prop :=
  ∀ (c d : Code) (hc : valid c = true) (hd : valid d = true),
    embeddingTest c d = true ↔ Nonempty ((toForest c hc).Carrier ↪o (toForest d hd).Carrier)

def ForestAvoidanceTestCorrect : Prop :=
  ∀ (U : List Code) (hU : FamilyValid U) (c : Code) (hc : valid c = true),
    permittedTest U c = true ↔ AvoidsForbidden (toFamily U hU) (toForest c hc).Carrier

def ForestBoundedHostTestCorrect : Prop :=
  ∀ (U : List Code) (hU : FamilyValid U) (c d : Code)
      (hc : valid c = true) (hd : valid d = true),
    boundedHostTest U c d = true ↔
      ∃ H : FiniteOrderForest, AvoidsForbidden (toFamily U hU) H.Carrier ∧
        Nonempty ((toForest c hc).Carrier ↪o H.Carrier) ∧
        Nonempty ((toForest d hd).Carrier ↪o H.Carrier)

def ForestNegativePairTestCorrect : Prop :=
  ∀ (U : List Code) (hU : FamilyValid U) (c d : Code)
      (hc : valid c = true) (hd : valid d = true),
    negativePairTest U c d = true ↔
      AvoidsForbidden (toFamily U hU) (toForest c hc).Carrier ∧
      AvoidsForbidden (toFamily U hU) (toForest d hd).Carrier ∧
      ¬ ∃ H : FiniteOrderForest, AvoidsForbidden (toFamily U hU) H.Carrier ∧
        Nonempty ((toForest c hc).Carrier ↪o H.Carrier) ∧
        Nonempty ((toForest d hd).Carrier ↪o H.Carrier)

/-- Genuine Primrec certificates on the explicit standard-coded finite data,
not a claim that arbitrary mathematical forest bundles are effective inputs. -/
def ForestFiniteTestsPrimitiveRecursive : Prop :=
  Primrec encode ∧ Primrec decode ∧
  Primrec allPairs ∧ Primrec allRelations ∧ Primrec hostCodes ∧
  Primrec₂ mapWords ∧ Primrec valid ∧
  Primrec (fun t : Code × Code × List ℕ => mapTest t.1 t.2.1 t.2.2) ∧
  Primrec₂ embeddingTest ∧ Primrec₂ permittedTest ∧
  Primrec (fun t : List Code × Code × Code => boundedHostTest t.1 t.2.1 t.2.2) ∧
  Primrec (fun t : List Code × Code × Code => negativePairTest t.1 t.2.1 t.2.2)

end LogicLineages.ModelsAlgebra.Forests.Targets
