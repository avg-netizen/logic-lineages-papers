import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.Paper16Targets
open Spine

/-- Paper16 ordering.tex, lem:elementary, all three printed assertions on the
reviewed typed, signature-valid, alpha-canonical presentation. -/
def Elementary : Prop :=
  (∀ S q t, (Weak S q t ∨ Strict S q t) → Ordinary t) ∧
  (∀ S q t, Strict S q t → Weak S q t) ∧
  (∀ S q σ, PaperTerm S q σ → Ordinary q → Weak S q q)

end LogicLineages.PersistentMarking.Paper16Targets
