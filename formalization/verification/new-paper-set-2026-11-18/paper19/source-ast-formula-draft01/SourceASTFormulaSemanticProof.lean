module
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaTargets
public import LogicLineages.ControlSensitivityCurrent.SourceASTTermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering

def ContSpec (p : AdmissibleSum.Policy) (f : Nat → Nat) {Δ m}
    (ν : Variable Δ .ground → Nat) (v : Fin m → Bool)
    (k : BooleanContinuation Δ m) (P : Bool → Prop) : Prop :=
  ∀ (Ξ : List Ty) (n : Nat) (s : Renaming Δ Ξ) (e : Fin m → Fin n)
    (μ : Variable Ξ .ground → Nat) (w : Fin n → Bool),
    (∀ x, μ (s x)=ν x) → (∀ i, w (e i)=v i) → ∀ root : Fin n,
    (k s e root).eval p f μ w ↔ P (w root)

theorem relation_semantic (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ Δ m}
    (a b : Term Γ) (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat)
    (ν : Variable Δ .ground → Nat) (hr : ∀ x, ν (r x)=ρ x) (v : Fin m → Bool)
    (node : ∀ {Ξ n}, Port Ξ → Port Ξ → InputNormalization.Node Ξ n)
    (op : Nat → Nat → Bool)
    (hop : ∀ (Ξ : List Ty) (n : Nat) (μ : Variable Ξ .ground → Nat) (w : Fin n → Bool)
      (x y : Port Ξ), (node x y).eval μ w = op (x.value (ExistentialPlan.inputs μ)) (y.value (ExistentialPlan.inputs μ)))
    (k : BooleanContinuation Δ m) (P : Bool → Prop) (hk : ContSpec p f ν v k P) :
    (emitRelation a b r node k).eval p f ν v ↔ P (op (a.eval p f ρ) (b.eval p f ρ)) := by
  apply term_semantic p f a r ρ ν hr v _ (fun x => P (op x (b.eval p f ρ)))
  intro Ξ s μ hs av
  apply term_semantic p f b (fun x => s (r x)) ρ μ (fun x => (hs (r x)).trans (hr x)) v _
    (fun y => P (op (av.value (ExistentialPlan.inputs μ)) y))
  intro Ω t ξ ht bv
  let z := (node (ExistentialPlan.portRename t av) bv).eval ξ v
  change (k (fun x => t (s x)) Fin.succ 0).eval p f ξ (Fin.cases z v) ↔ _
  rw [hk Ω (m+1) (fun x => t (s x)) Fin.succ ξ (Fin.cases z v)
    (fun x => (ht (s x)).trans (hs x)) (fun _ => rfl) 0]
  change P z ↔ _
  rw [show z = op ((ExistentialPlan.portRename t av).value (ExistentialPlan.inputs ξ))
      (bv.value (ExistentialPlan.inputs ξ)) from hop Ω m ξ v _ _,
    InputNormalization.portRename_value t μ ξ ht av]

theorem formula_semantic (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ} (a : Formula Γ) :
    ∀ {Δ m} (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
    (∀ x, ν (r x)=ρ x) → ∀ (v : Fin m → Bool) (k : BooleanContinuation Δ m) (P : Bool → Prop),
    ContSpec p f ν v k P → ((a.emit r k).eval p f ν v ↔ P (a.eval p f ρ)) := by
  induction a with
  | truth =>
      intro Δ m r ρ ν hr v k P hk
      exact hk Δ (m+1) (fun x => x) Fin.succ ν (Fin.cases true v) (fun _ => rfl) (fun _ => rfl) 0
  | falsity =>
      intro Δ m r ρ ν hr v k P hk
      exact hk Δ (m+1) (fun x => x) Fin.succ ν (Fin.cases false v) (fun _ => rfl) (fun _ => rfl) 0
  | eq a b =>
      intro Δ m r ρ ν hr v k P hk
      exact relation_semantic p f a b r ρ ν hr v (fun x y => .eq x y)
        (fun x y => decide (x=y)) (fun _ _ _ _ _ _ => rfl) k P hk
  | le a b =>
      intro Δ m r ρ ν hr v k P hk
      exact relation_semantic p f a b r ρ ν hr v (fun x y => .le x y)
        (fun x y => decide (x≤y)) (fun _ _ _ _ _ _ => rfl) k P hk
  | lt a b =>
      intro Δ m r ρ ν hr v k P hk
      exact relation_semantic p f a b r ρ ν hr v (fun x y => .lt x y)
        (fun x y => decide (x<y)) (fun _ _ _ _ _ _ => rfl) k P hk
  | neg a ih =>
      intro Δ m r ρ ν hr v k P hk
      apply ih r ρ ν hr v _ (fun b => P (!b))
      intro Ξ n s e μ w hs he root
      exact hk Ξ (n+1) s (fun i => (e i).succ) μ (Fin.cases (!(w root)) w)
        hs (fun i => he i) 0
  | conj a b iha ihb =>
      intro Δ m r ρ ν hr v k P hk
      apply iha r ρ ν hr v _ (fun z => P (z && b.eval p f ρ))
      intro Ξ n s e μ w hs he left
      apply ihb (fun x => s (r x)) ρ μ (fun x => (hs (r x)).trans (hr x)) w _
        (fun z => P (w left && z))
      intro Ω l t h ξ u ht hh right
      have hx := hk Ω (l+1) (fun x => t (s x)) (fun i => (h (e i)).succ) ξ
        (Fin.cases (u (h left) && u right) u)
        (fun x => (ht (s x)).trans (hs x)) (fun i => (hh (e i)).trans (he i)) 0
      simpa only [Formula.emit,InputNormalization.Input.eval,InputNormalization.Node.eval,Fin.cases_zero,hh] using hx
  | disj a b iha ihb =>
      intro Δ m r ρ ν hr v k P hk
      apply iha r ρ ν hr v _ (fun z => P (z || b.eval p f ρ))
      intro Ξ n s e μ w hs he left
      apply ihb (fun x => s (r x)) ρ μ (fun x => (hs (r x)).trans (hr x)) w _
        (fun z => P (w left || z))
      intro Ω l t h ξ u ht hh right
      have hx := hk Ω (l+1) (fun x => t (s x)) (fun i => (h (e i)).succ) ξ
        (Fin.cases (u (h left) || u right) u)
        (fun x => (ht (s x)).trans (hs x)) (fun i => (hh (e i)).trans (he i)) 0
      simpa only [Formula.emit,InputNormalization.Input.eval,InputNormalization.Node.eval,Fin.cases_zero,hh] using hx

theorem cps : SourceASTFormulaTargets.CPS := by
  intro p f Γ Δ r ρ ν hr m v a k P hk
  exact formula_semantic p f a r ρ ν hr v k P hk
end LogicLineages.ControlSensitivityCurrent.SourceAST
