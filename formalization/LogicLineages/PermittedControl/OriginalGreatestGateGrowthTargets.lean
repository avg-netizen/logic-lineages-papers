module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
public import LogicLineages.PermittedControl.ActualCountLeadingErrorTargets
public import LogicLineages.PermittedControl.SelectedLeadingSignCutoffTargets
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalGreatestGateGrowth
open OrdinalComparison FieldComparison PreparedProjection
open OriginalNaturalFieldGates (Gate)
open SelectedNonlinearImageBounds (NonlinearField)

def longCountBoundCode (lam mu : Nat) : Nat :=
  let R := rawNormCode mu
  let κ : Int := 1 - (((R+1)/2 : Nat) : Int)
  max (rawNormCode lam) (max (R+3) (SelectedLeadingSignCutoff.cutoff 2 κ.natAbs))

def longCountBound (lam mu : NONote) : Nat :=
  longCountBoundCode (rawNoteEncode lam.1) (rawNoteEncode mu.1)

def ExactLongCountBound : Prop :=
  ∀ lam mu : NONote,
    longCountBound lam mu = max (actualOrdinalNorm lam.1.repr)
      (max (actualOrdinalNorm mu.1.repr+3)
        (SelectedLeadingSignCutoff.cutoff 2 (Targets.countCoreConstant mu.1.repr).natAbs))

def ExactOrdinaryStrictGrowth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (r : Nat) (F : ValueField) (v : Nat),
      NonlinearField F → LowerOperandActual f ρ (.ordinary r F) v → ρ r < v

def ExactLimitCollapseStrictGrowth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (head x v : Nat), FixedHeadCollapseGraph.read f (head,x) = some v → x < v

/-- Uniform above the actual syntax cutoff, including the short count
prefix identity case in the actual long count core theorem. -/
def ExactLongCountStrictGrowth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (r : Nat) (lam mu : NONote) (v y : Nat),
      LongField (.entry 0 lam mu) → longCountBound lam mu ≤ ρ r →
      y ≤ ρ r → LowerOperandActual f ρ (.count r lam mu) v →
        0 < (v : Int) - (y : Int)

def ExactShortCountGraph : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (θ : Nat → Nat) (lam mu : NONote) (source out : Nat),
      0 < shortGapLength lam mu →
        ((Gate.count (.proper lam mu) source out).graph f θ ↔
          ProperField (.entry 0 lam mu) ∧ actualOrdinalNorm lam.1.repr ≤ θ source ∧
            θ out = shortGapLength lam mu)

def FullOriginalGreatestGateGrowth : Prop :=
  ExactLongCountBound ∧ ExactOrdinaryStrictGrowth ∧ ExactLimitCollapseStrictGrowth ∧
    ExactLongCountStrictGrowth ∧ ExactShortCountGraph

end LogicLineages.PermittedControl.OriginalGreatestGateGrowth
