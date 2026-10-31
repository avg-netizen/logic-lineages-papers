module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.Targets
open CotreeGrammarFlow

def TreeBalance : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q (t : Tree δ q) r,
    consumed δ (counts t) r + (holes t).count r =
      (if q = r then 1 else 0) + produced (counts t) r

def TreeTerminals : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q (t : Tree δ q),
    (∀ B, terminalTotal (counts t) B = (word t).count B) ∧
    (∀ B r, r ∉ B → (counts t).terminal (B,r) = 0)

def ClosedBuilds : Prop :=
  ∀ (Q : Type) (δ : Q → Q → Q) q (t : Tree δ q),
    holes t = [] → CotreeGrammar.Builds δ q (word t)

def BuildsClosedTree : Prop :=
  ∀ (Q : Type) (δ : Q → Q → Q) q w, CotreeGrammar.Builds δ q w →
    ∃ t : Tree δ q, holes t = [] ∧ word t = w

def PlugCounts : Prop :=
  ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) r q (C : Context δ r q) (t : Tree δ q),
    counts (plug C t) = addCounts (contextCounts C) (counts t)

def HoleFactorization : Prop :=
  ∀ (Q : Type) (δ : Q → Q → Q) r (t : Tree δ r) q,
    q ∈ holes t ↔ ∃ C : Context δ r q, plug C (.hole q) = t

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.Targets
