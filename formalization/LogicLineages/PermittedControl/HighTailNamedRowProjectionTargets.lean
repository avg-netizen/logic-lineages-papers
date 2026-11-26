module
public import LogicLineages.PermittedControl.MixedRankNamedResidueRowTargets
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailNamedRowProjection
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode properOperand)
open MixedRankResidue (rankSupport)
open MixedRankNamedResidueRow (RawArgs rawArgs prepareCode requests row slots)
open SignedRowCoordinateSlice (denotes)

abbrev ProjectionArgs := Nat × Nat × RawArgs

def coordinateTail (B m : Nat) (terms : List WeightedOperand) : Nat :=
  weightedTailCode B m (terms.map encodeWeighted)

def lowerGuard (name bound : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-(bound : Int),[(1,.variable name)]))

def lowerGuardCode (name bound : Nat) : Nat :=
  let data : NormalForm.Code.AtomData := (0,0,-(bound : Int),[(1,(0,name,0,0))])
  6 * Encodable.encode data + 2

noncomputable def guarded (B m name : Nat) (c : Int) (terms : List WeightedOperand) : NormalForm.Formula :=
  .conjunction (lowerGuard name (coordinateTail B m terms)) (row m c terms)

noncomputable def projected (B m name : Nat) (c : Int) (terms : List WeightedOperand) : NormalForm.Formula :=
  LinearRows.eliminate name (guarded B m name c terms)

/-- Preserve the original request bytes. The eliminated name may remain as
an unused table position, but it does not occur in the result formula. -/
def projectCode (p : ProjectionArgs) : Option (List NamedCode × Nat) :=
  let (B,name,q) := p
  let bound := weightedTailCode B q.1 q.2.2
  (prepareCode q).map (fun packet =>
    (packet.1,LinearRows.Code.eliminate name (6 * Nat.pair (lowerGuardCode name bound) packet.2 + 4)))

def CodeExact : Prop :=
  Primrec projectCode ∧ (∀ p : ProjectionArgs, p.2.2.1 = 0 → projectCode p = none) ∧
  ∀ (B m name : Nat) (c : Int) (terms : List WeightedOperand), 0 < m →
    projectCode (B,name,rawArgs m c terms) =
      some ((requests terms).map encodeRequest,(projected B m name c terms).encode)

def OutputSupport : Prop :=
  ∀ (B m name : Nat) (c : Int) (terms : List WeightedOperand),
    LinearRows.isLinear name (guarded B m name c terms) = true ∧
    ∀ i : Nat, i ∈ (projected B m name c terms).variables ↔
      i ≠ name ∧ i ∈ (row m c terms).variables

/-- The positive name must be the actual selected rank's own generated
slot. The eliminated raw value pays the same tail as each other used rank. -/
def ActualProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m name rank : Nat) (c : Int) (terms : List WeightedOperand) (ρ ν : Nat → Nat),
    0 < m → (name,rank) ∈ slots terms → (∀ t ∈ terms, properOperand t.2) →
    (∀ r ∈ rankSupport terms, r ≠ rank → coordinateTail B m terms ≤ ρ r) →
    (∀ s ∈ slots terms, s.1 ≠ name → ν s.1 = ρ s.2) →
    ((projected B m name c terms).eval ν ↔
      ∃ z : Nat, coordinateTail B m terms ≤ z ∧
        denotes f (Function.update ρ rank z) m c terms)

def FullHighTailNamedRowProjection : Prop := CodeExact ∧ OutputSupport ∧ ActualProjection

end LogicLineages.PermittedControl.HighTailNamedRowProjection
