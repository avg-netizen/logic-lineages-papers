module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof
open ParametricSourceEraser SourceCollisionCompletion

theorem eraser_scalar (b : Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) (x y : Nat)
    (hp : Scalar (SourceMachineControlNonperiodicity.gamma b) ν p x)
    (hq : Scalar (SourceMachineControlNonperiodicity.gamma b) ν q y) :
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν (eraser p q) (g b (3*x+y+2)) := by
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have he := (ParametricSourceEraser.Proof.genericFiniteClosure _ h.1 h.2.1 Γ ν p q x y hp hq).1
  simpa only [g_calibration,Nat.add_assoc] using he

theorem actualSourceCollision : Targets.ActualSourceCollision := by
  intro b Γ ν p q x y hp hq
  have hpp := eraser_scalar b ν p p x x hp hp
  have hqq := eraser_scalar b ν q q y y hq hq
  have hpq := eraser_scalar b ν p q x y hp hq
  have hqp := eraser_scalar b ν q p y x hq hp
  have hl : Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorLeft p q) (leftValue b x y) :=
    eraser_scalar b ν _ _ _ _ hpp hqq
  have hr : Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorRight p q) (rightValue b x y) :=
    eraser_scalar b ν _ _ _ _ hpq hqp
  refine ⟨hl,hr,?_⟩
  intro l r hL hR
  have el := ParametricSourceEraser.Proof.scalar_unique _ ν _ _ _ hL hl
  have er := ParametricSourceEraser.Proof.scalar_unique _ ν _ _ _ hR hr
  rw [el,er]
  exact numericCollision b x y
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof
