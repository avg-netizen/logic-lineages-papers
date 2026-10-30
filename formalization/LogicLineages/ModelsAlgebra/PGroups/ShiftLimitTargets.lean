module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftGroupDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe v

def groupShiftExponent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ShiftGroup p), p ^ 2 • x = 0

def groupShiftLimitSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (z : EndomorphismLimit (shiftHom p)), p • z = 0 →
    ∃ y : EndomorphismLimit (shiftHom p), p • y = z

/-- Nonisomorphism is proved from an actual root obstruction, not assumed. -/
def groupShiftLimitNotIsomorphic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ¬ Nonempty (ShiftGroup p ≃+ EndomorphismLimit (shiftHom p))

/-- Actual source subfamily C_p + countably many C_(p²): no relative Pi2
Scott sentence, witnessed by the constructed countable direct limit. -/
def groupShiftNoPiTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (φ : Formula 0),
    Complexity .pi (2 : Ordinal.{v}) φ → ¬ GroupScottSentence (ShiftGroup p) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
