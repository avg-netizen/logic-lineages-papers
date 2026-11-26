module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ExplicitHalfGraph
open OrdinalComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

/-- The optional natural half is an explicit graph slot. The two signed
rows assert equality to the actual full value at its separate slot. -/
def graph (full half : Nat) : NormalForm.Formula :=
  .conjunction (.atom (.nonnegative (0,[(2,.variable half),(-1,.variable full)])))
    (.atom (.nonnegative (0,[(1,.variable full),(-2,.variable half)])))

def atLeastData (full half : Nat) : NormalForm.Code.AtomData :=
  (0,0,0,[(2,(0,half,0,0)),(-1,(0,full,0,0))])

def atMostData (full half : Nat) : NormalForm.Code.AtomData :=
  (0,0,0,[(1,(0,full,0,0)),(-2,(0,half,0,0))])

def graphCode (full half : Nat) : Nat :=
  6 * Nat.pair (6 * Encodable.encode (atLeastData full half) + 2)
    (6 * Encodable.encode (atMostData full half) + 2) + 4

def CodeExact : Prop := Primrec₂ graphCode ∧ ∀ full half : Nat, graphCode full half = (graph full half).encode

def NaturalGraph : Prop := ∀ (full half : Nat) (ν : Nat → Nat),
  (graph full half).eval ν ↔ 2 * ν half = ν full

/-- The original one-iterate field at the raw input supplies the full
value. The fresh half slot has its unique actual natural graph extension. -/
def ActualHalfExtension : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (rank full half : Nat) (ρ : Nat → Nat), full ≠ half →
    ∃ value : Nat, value = f (ρ rank) ∧
      LowerOperandActual f ρ (.ordinary rank (.iterate 1)) value ∧
      lowerOperandRead f ρ (.ordinary rank (.iterate 1)) = some (some value) ∧
      ∀ ν : Nat → Nat, ν full = value →
        (∀ h : Nat, (graph full half).eval (Function.update ν half h) ↔ h = value / 2) ∧
        (∃! h : Nat, (graph full half).eval (Function.update ν half h)) ∧
        ∀ (h name : Nat), name ≠ half → Function.update ν half h name = ν name

def FullExplicitHalfGraph : Prop := CodeExact ∧ NaturalGraph ∧ ActualHalfExtension

end LogicLineages.PermittedControl.ExplicitHalfGraph
