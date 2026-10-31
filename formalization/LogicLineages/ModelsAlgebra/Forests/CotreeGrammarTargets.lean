module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.Targets

def RulesExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (R : ContextFreeRule (Finset Q) Q),
    R ∈ rules δ ↔ (∃ r s, binaryRule δ r s = R) ∨
      ∃ B q, q ∈ B ∧ terminalRule q B = R

/-- Exact correspondence with actual Mathlib context-free derivations,
not a grammar correctness assumption. Every word occurrence is retained. -/
def GrammarLanguageExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q w,
    w ∈ (grammar δ q).language ↔ Builds δ q w

def SkeletonNonempty : Prop :=
  ∀ (Q : Type) (δ : Q → Q → Q) q w, Builds δ q w → w ≠ []

/-- Child occurrences match with their complete multiplicity. This statement
is a finite grammar/skeleton fact, not an effective Parikh conversion. -/
def CountPermutationExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q children,
    (∃ w, w ∈ (grammar δ q).language ∧ ∀ B, counts w B = counts children B) ↔
      ∃ w, Builds δ q w ∧ w.Perm children

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.Targets
