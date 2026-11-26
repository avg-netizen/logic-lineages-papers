module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OrdinaryResidueOperand
open OrdinalComparison FieldComparison PreparedProjection

def doubledFloor (j a : Nat) : Int :=
  2 * ((j / 2 : Nat) : Int) - 2 * (a : Int)

def doubledCeiling (n a : Nat) : Int :=
  2 * (((n + 1) / 2 : Nat) : Int) - 2 * (a : Int)

/-- Signed output on a single shared raw residue. Bare identity retains
the raw numeral and its parity. Entry fields retain the outer iterate. -/
noncomputable def residue (F : ValueField) (j : Nat) : Int :=
  match F with
  | .iterate 0 => (j : Int)
  | .iterate (a+1) => doubledFloor j (a+1)
  | .entry a lam mu =>
    let k := shortGapLength lam mu
    if k = 0 then doubledCeiling (actualOrdinalNorm mu.1.repr) a else doubledFloor j (k+a)

noncomputable def residueTail (B m : Nat) : ValueField → Nat
  | .iterate 0 => 0
  | .iterate (_+1) => max m B
  | .entry _ lam mu =>
    max (actualOrdinalNorm lam.1.repr) (max (actualOrdinalNorm mu.1.repr + 3) (max m B))

/-- An arithmetic program on arbitrary raw numerals. Source interpretation
is calibrated separately against the original canonical ValueField code. -/
def residueCode (F : LongFieldCode) (j : Nat) : Int :=
  let (tag,a,lam,mu) := F
  if tag = 0 then
    if a = 0 then (j : Int) else doubledFloor j a
  else
    let k := shortGapLengthCode lam mu
    if k = 0 then doubledCeiling (rawNormCode mu) a else doubledFloor j (k+a)

def residueTailCode (B m : Nat) (F : LongFieldCode) : Nat :=
  let (tag,a,lam,mu) := F
  if tag = 0 then
    if a = 0 then 0 else max m B
  else CountCongruenceNamedRow.tailCode B lam mu m

def CodeExact : Prop :=
  Primrec₂ residueCode ∧
  Primrec (fun p : Nat × Nat × LongFieldCode => residueTailCode p.1 p.2.1 p.2.2) ∧
  (∀ (F : ValueField) j, residueCode (longFieldCode F) j = residue F j) ∧
  (∀ (B m : Nat) (F : ValueField), residueTailCode B m (longFieldCode F) = residueTail B m F)

/-- Actual value, domain and read are obtained at the same original
coordinate. The shared residue is that coordinate modulo 2m. -/
def ActualResidue : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (m rank : Nat) (F : ValueField) (ρ : Nat → Nat),
      0 < m → ProperField F →
      residueTailCode B m (longFieldCode F) ≤ ρ rank →
        ∃ v : Nat,
          LowerOperandActual f ρ (.ordinary rank F) v ∧
          lowerOperandRead f ρ (.ordinary rank F) = some (some v) ∧
          Int.ModEq (2 * (m : Int)) (v : Int) (residue F (ρ rank % (2*m)))

def FullOrdinaryResidueOperand : Prop := CodeExact ∧ ActualResidue

end LogicLineages.PermittedControl.OrdinaryResidueOperand
