module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserTargets
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionAtomicProof
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionEraserProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Proof
open ParametricSourceSuccessor

theorem fullAssignmentClosure : Targets.FullAssignmentClosure := by
  intro Γ p q vp vq hp hq
  exact SourceCollisionCompletion.Proof.eraser_assignment p q vp vq hp hq

theorem eraser_value (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n)
    {Γ} (ν : OrdinalComponent Γ → Ordinal) (a b : OrdinalExpression Γ) (x y : Nat)
    (ha : denoteWith G ν a=(x : Ordinal)) (hb : denoteWith G ν b=(y : Ordinal)) :
    denoteWith G ν (eraserVector a b 0)=((G (3*x+y+4)+1 : Nat) : Ordinal) := by
  have h1 : denoteWith G ν (.one : OrdinalExpression Γ)=((1 : Nat) : Ordinal) := by simp [denoteWith]
  have ha1 := ParametricSourceAddition.Proof.add_value G ν _ _ _ _ ha h1
  have haa := ParametricSourceAddition.Proof.add_value G ν _ _ _ _ ha1 ha1
  have haaa := ParametricSourceAddition.Proof.add_value G ν _ _ _ _ haa ha
  have ht := ParametricSourceAddition.Proof.add_value G ν _ _ _ _ haaa hb
  have hc := ParametricSourceAddition.Proof.collapse_one_value G hm hi ν _ _ ht
  have hn : x+1+(x+1)+x+y+2=3*x+y+4 := by omega
  simpa only [eraserVector,inflated,hn] using hc

theorem scalar_unique (G : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (t : OriginalTerm Γ .ground) (x y : Nat) (hx : Scalar G ν t x) (hy : Scalar G ν t y) : x=y := by
  obtain ⟨vx,hvx,hex⟩ := hx
  obtain ⟨vy,hvy,hey⟩ := hy
  cases Option.some.inj (hvx.symm.trans hvy)
  exact Nat.cast_injective (hex.symm.trans hey)

theorem genericFiniteClosure : Targets.GenericFiniteClosure := by
  intro G hm hi Γ ν p q x y hp hq
  obtain ⟨vp,hvp,hep⟩ := hp
  obtain ⟨vq,hvq,heq⟩ := hq
  have hr : Scalar G ν (SourceCollisionCompletion.eraser p q) (G (3*x+y+4)+1) :=
    ⟨eraserVector (vp 0) (vq 0),fullAssignmentClosure Γ p q vp vq hvp hvq,
      eraser_value G hm hi ν (vp 0) (vq 0) x y hep heq⟩
  refine ⟨hr,?_⟩
  intro z
  constructor
  · intro hz
    exact scalar_unique G ν _ _ _ hz hr
  · rintro rfl
    exact hr
end LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Proof
