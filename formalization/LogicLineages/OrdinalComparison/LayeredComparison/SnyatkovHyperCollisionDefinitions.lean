module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision

/-- Signed source shifts, with a total numerical default below the genuine
domain. The tail-domain gate proves no truncation at every large original input. -/
def shiftedInput (u : Nat) (e : Int) : Nat :=
  ((FixedSeedControlResidue.H u : Int) + e).toNat

def translatedValue (u : Nat) (e : Int) : Nat := Phi (shiftedInput u e)

/-- Explicit source Lemma4 threshold; both original signed offsets retained. -/
def collisionBound (c : Nat) (e k : Int) : Nat :=
  c + e.natAbs + k.natAbs + 1

def boundCode (p : Nat × Int × Int) : Nat := collisionBound p.1 p.2.1 p.2.2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision
