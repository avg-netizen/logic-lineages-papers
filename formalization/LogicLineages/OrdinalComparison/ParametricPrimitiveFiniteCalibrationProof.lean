module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteTargets
public import LogicLineages.OrdinalComparison.ParametricSourceEraserProof
public import LogicLineages.OrdinalComparison.ParametricSourceOneProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof
open PrimitiveLowering ParametricSourceEraser ParametricSourceSuccessor

theorem port_value (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat) (a : Port Γ) :
    denoteWith G (positive ρ) (PrimitiveLowering.Proof.portExpression a) =
      ((a.value ρ+1 : Nat) : Ordinal) := by
  cases a <;> simp [PrimitiveLowering.Proof.portExpression,Port.value,
    SourceSortCompletion.input,denoteWith,positive]

theorem expression_value (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat,n ≤ G n)
    {Γ} (ρ : OrdinalComponent Γ → Nat) (e : Expr Γ) :
    Scalar G (positive ρ) e.term (value G ρ e+1) := by
  have h1 : denoteWith G (positive ρ) (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by
    simp [denoteWith]
  cases e with
  | port a => exact ⟨_,PrimitiveLowering.Proof.port_assignment a,port_value G ρ a⟩
  | successor a =>
    refine ⟨_,PrimitiveLowering.Proof.successor_assignment a,?_⟩
    have ht := ParametricSourceAddition.Proof.add_value G (positive ρ) _ _ _ _ h1 (port_value G ρ a)
    have hc := ParametricSourceAddition.Proof.collapse_one_value G hm hi (positive ρ) _ _ ht
    have hn : 1+(a.value ρ+1)+2=a.value ρ+4 := by omega
    simpa only [value,hn] using hc
  | erase a b =>
    refine ⟨_,ParametricSourceAddition.Proof.eraser_assignment a b,?_⟩
    exact ParametricSourceAddition.Proof.eraser_value G hm hi ρ a b
  | identityZero =>
    refine ⟨_,ParametricSourceOne.Proof.identity_assignment Γ,?_⟩
    have h2 := ParametricSourceAddition.Proof.add_value G (positive ρ) _ _ _ _ h1 h1
    have h3 := ParametricSourceAddition.Proof.add_value G (positive ρ) _ _ _ _ h2 h1
    have h4 := ParametricSourceAddition.Proof.add_value G (positive ρ) _ _ _ _ h3 h1
    exact ParametricSourceAddition.Proof.collapse_one_value G hm hi (positive ρ) _ _ h4

theorem exactExpressionCalibration : Targets.ExactExpressionCalibration := by
  intro G hm hi Γ ρ e
  have he := expression_value G hm hi ρ e
  refine ⟨he,fun n => ⟨fun hn => ParametricSourceEraser.Proof.scalar_unique G _ _ _ _ hn he,?_⟩⟩
  intro hn
  simpa only [hn] using he
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof
