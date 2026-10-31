module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest
open CotreeGrammarFlow CotreeGrammarOpen

abbrev Packed {Q : Type} (δ : Q → Q → Q) := Σ q, Tree δ q

def forestCounts {Q : Type} [DecidableEq Q] {δ : Q → Q → Q} (F : List (Packed δ)) : Counts Q :=
  ⟨fun p => (F.map (fun t => (counts t.2).binary p)).sum,
    fun p => (F.map (fun t => (counts t.2).terminal p)).sum⟩

def roots {Q : Type} {δ : Q → Q → Q} (F : List (Packed δ)) : List Q := F.map Sigma.fst

def forestHoles {Q : Type} {δ : Q → Q → Q} (F : List (Packed δ)) : List Q :=
  F.flatMap (fun t => holes t.2)

def forestWord {Q : Type} {δ : Q → Q → Q} (F : List (Packed δ)) : List (Finset Q) :=
  F.flatMap (fun t => word t.2)

/-- Distinct forest occurrences cannot be glued at a matching root/hole.
Permutation exposes two distinct occurrences even when their trees are equal. -/
def NoCrossHole {Q : Type} {δ : Q → Q → Q} (F : List (Packed δ)) : Prop :=
  ∀ a (ta : Tree δ a) b (tb : Tree δ b) rest,
    F.Perm (⟨a,ta⟩ :: ⟨b,tb⟩ :: rest) → b ∉ holes ta

/-- Zero-production hole-only components are excluded as well. -/
def NoBareHole {Q : Type} {δ : Q → Q → Q} (F : List (Packed δ)) : Prop :=
  ∀ q, (⟨q, Tree.hole q⟩ : Packed δ) ∉ F

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest
