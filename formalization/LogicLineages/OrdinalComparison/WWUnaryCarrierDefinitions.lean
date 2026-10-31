module
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
public import LogicLineages.OrdinalComparison.WWGroundClosingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnaryCarrier

/-- The first positive component exists at every nonempty ground-arrow type. -/
def headIndex (r : Nat) : Fin ((Ty.curriedGround (r+1)).level+1) :=
  ⟨1, by change 1 < max (0+1) (Ty.curriedGround r).level+1; omega⟩

/-- Replace the tracked head name globally by one fresh same-type name.
The old tracked slot remains unused; every other name keeps its identity. -/
def renameTracked {Γ : List Ty} {σ : Ty} : Renaming (σ :: Γ) (σ :: σ :: Γ)
  | _, .here => .here
  | _, .there x => .there (.there x)

/-- Saturate by exactly r literal zero arguments, retaining a unary result.
This traverses no opaque source internals and performs no beta reduction. -/
def saturate {Γ : List Ty} : (r : Nat) →
    OriginalTerm Γ (Ty.curriedGround (r+1)) → OriginalTerm Γ (Ty.curriedGround 1)
  | 0, t => t
  | r+1, t => saturate r (.app t .zeroC)

/-- Close all free ground captures, retaining every functional name. Unused
ground context slots are retained, but their occurrences become literal zero.
The source substitution lifts under arbitrary internal binders. -/
def groundMap (Γ : List Ty) : GroundClosing.GroundMap Γ Γ
  | .ground, _ => .zero
  | .arrow _ _, x => .var x

def closeGround {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) : OriginalTerm Γ τ :=
  t.substitute (GroundClosing.GroundMap.source (groundMap Γ))

/-- Actual unary source with fresh tracked name, literal saturation, and
closed ground captures. Its scalar is the actual scalar of this source. -/
def carrier {Γ : List Ty} {k r : Nat}
    (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1))) :
    OriginalTerm (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround 1) :=
  closeGround (saturate r (t.rename renameTracked))
end LogicLineages.OrdinalComparison.Source.UnaryCarrier
