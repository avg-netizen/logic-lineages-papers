module
public import LogicLineages.ControlSensitivityCurrent.SourceASTObservationProof
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering

theorem term_semantic (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ} (e : Term Γ) :
    ∀ {Δ m} (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
    (∀ x, ν (r x)=ρ x) → ∀ (v : Fin m → Bool) (k : Continuation Δ m) (P : Nat → Prop),
    (∀ (Ξ : List Ty) (s : Renaming Δ Ξ) (μ : Variable Ξ .ground → Nat),
      (∀ x, μ (s x)=ν x) → ∀ a : Port Ξ,
      (k s a).eval p f μ v ↔ P (a.value (ExistentialPlan.inputs μ))) →
    ((e.emit r k).eval p f ν v ↔ P (e.eval p f ρ)) := by
  induction e with
  | var x =>
      intro Δ m r ρ ν h v k P hk
      simpa only [Term.emit,Term.eval,Port.value,SourceSortCompletion.input,ExistentialPlan.inputs,h] using
        hk Δ (fun y => y) ν (fun _ => rfl) (.var (r x))
  | literal n =>
      intro Δ m r ρ ν h v k P hk
      exact hk _ (Renaming.weaken Δ .ground) (ExistentialPlan.extend ν n) (fun _ => rfl) (.var .here)
  | observation t =>
      intro Δ m r ρ ν h v k P hk
      change (k _ (.var .here)).eval p f (ExistentialPlan.extend ν
        (InputNormalization.sourceValue p f ν (ScopedDAG.renameInput r t))) v ↔ _
      rw [hk _ _ _ (fun _ => rfl)]
      change P (InputNormalization.sourceValue p f ν (ScopedDAG.renameInput r t)) ↔
        P (InputNormalization.sourceValue p f ρ t)
      rw [sourceValue_rename p f r ρ ν h]
  | add a b iha ihb =>
      intro Δ m r ρ ν h v k P hk
      apply (iha r ρ ν h v _ (fun z => P (z+b.eval p f ρ)) ?_)
      intro Ξ s μ hs av
      apply (ihb (fun x => s (r x)) ρ μ (fun x => (hs (r x)).trans (h x)) v _
        (fun z => P (av.value (ExistentialPlan.inputs μ)+z)) ?_)
      intro Ω t ξ ht bv
      change (k (fun x => .there (t (s x))) (.var .here)).eval p f
        (ExistentialPlan.extend ξ ((ExistentialPlan.portRename t av).value (ExistentialPlan.inputs ξ)+
          bv.value (ExistentialPlan.inputs ξ))) v ↔ _
      rw [hk _ _ _ (fun x => (ht (s x)).trans (hs x))]
      change P ((ExistentialPlan.portRename t av).value (ExistentialPlan.inputs ξ)+
        bv.value (ExistentialPlan.inputs ξ)) ↔
        P (av.value (ExistentialPlan.inputs μ)+bv.value (ExistentialPlan.inputs ξ))
      rw [InputNormalization.portRename_value t μ ξ ht av]
  | unary h a ih =>
      intro Δ m r ρ ν hr v k P hk
      apply (ih r ρ ν hr v _ (fun z => P (callValue p f h z)) ?_)
      intro Ξ s μ hs av
      let z := av.value (ExistentialPlan.inputs μ)
      let ξ := ExistentialPlan.extend μ z
      let w := InputNormalization.sourceValue p f ξ (BooleanCompiler.call h .here)
      change (k (fun x => .there (.there (s x))) (.var .here)).eval p f
        (ExistentialPlan.extend ξ w) v ↔ P (callValue p f h z)
      rw [hk (.ground::.ground::Ξ) (fun x => .there (.there (s x)))
        (ExistentialPlan.extend ξ w) (fun x => hs x) (.var .here)]
      change P w ↔ P (callValue p f h z)
      have hw : w = callValue p f h z := call_value p f ξ h .here
      rw [hw]

theorem semantic : SourceASTTermTargets.Semantic := by
  intro p f Γ Δ r ρ ν h m v e k P hk
  exact term_semantic p f e r ρ ν h v k P hk

theorem cost : SourceASTTermTargets.Cost := by
  intro Γ Δ m r e
  induction e generalizing Δ with
  | var x =>
      intro k K hk
      simpa [Term.emit,Term.cost] using hk Δ (fun y => y) (.var (r x))
  | literal n =>
      intro k K hk
      have hh := hk _ (Renaming.weaken Δ .ground) (.var .here)
      simpa only [Term.emit,InputNormalization.Input.cost,Term.cost] using Nat.add_le_add_left hh (Nat.log2 n+2)
  | observation t =>
      intro k K hk
      have hh := hk _ (Renaming.weaken Δ .ground) (.var .here)
      simpa only [Term.emit,InputNormalization.Input.cost,Term.cost] using Nat.add_le_add_left hh 1
  | add a b iha ihb =>
      intro k K hk
      have hh := iha Δ r (fun s av => b.emit (fun x => s (r x)) (fun t bv =>
        .add (ExistentialPlan.portRename t av) bv
          (k (fun x => .there (t (s x))) (.var .here)))) (b.cost+1+K) (by
        intro Ξ s av
        have hb := ihb Ξ (fun x => s (r x)) (fun t bv =>
          .add (ExistentialPlan.portRename t av) bv
            (k (fun x => .there (t (s x))) (.var .here))) (1+K) (by
          intro Ω t bv
          have h := hk _ (fun x => .there (t (s x))) (.var .here)
          exact Nat.add_le_add_left h 1)
        simpa [Nat.add_assoc] using hb)
      simpa [Term.emit,Term.cost,Nat.add_assoc] using hh
  | unary h a ih =>
      intro k K hk
      have hh := ih Δ r (fun s av => .add av .zero
        (.unary h .here (k (fun x => .there (.there (s x))) (.var .here)))) (4+K) (by
        intro Ξ s av
        have h := hk (.ground::.ground::Ξ) (fun x => .there (.there (s x))) (.var .here)
        simpa only [InputNormalization.Input.cost, ← Nat.add_assoc] using
          Nat.add_le_add_left (Nat.add_le_add_left h 3) 1)
      simpa [Term.emit,Term.cost,Nat.add_assoc] using hh

theorem sourceTables : SourceASTTermTargets.SourceTables := by
  intro Γ Δ m r e
  induction e generalizing Δ with
  | var x =>
      intro k M hk
      simpa [Term.emit,Term.sourceMax] using hk Δ (fun y => y) (.var (r x))
  | literal n =>
      intro k M hk
      simpa [Term.emit,Term.sourceMax,InputNormalization.Input.sourceMax] using
        hk _ (Renaming.weaken Δ .ground) (.var .here)
  | observation t =>
      intro k M hk
      have hh := hk _ (Renaming.weaken Δ .ground) (.var .here)
      simp only [Term.emit,Term.sourceMax,InputNormalization.Input.sourceMax,
        (ScopedDAG.Proof.«renaming» Γ Δ .ground r t).2]
      exact max_le_max_left _ hh
  | add a b iha ihb =>
      intro k M hk
      have hh := iha Δ r (fun s av => b.emit (fun x => s (r x)) (fun t bv =>
        .add (ExistentialPlan.portRename t av) bv
          (k (fun x => .there (t (s x))) (.var .here)))) (max b.sourceMax M) (by
        intro Ξ s av
        exact ihb Ξ (fun x => s (r x)) (fun t bv =>
          .add (ExistentialPlan.portRename t av) bv
            (k (fun x => .there (t (s x))) (.var .here))) M (by
          intro Ω t bv
          exact hk _ (fun x => .there (t (s x))) (.var .here)))
      simpa [Term.emit,Term.sourceMax,max_assoc] using hh
  | unary h a ih =>
      intro k M hk
      have hh := ih Δ r (fun s av => .add av .zero
        (.unary h .here (k (fun x => .there (.there (s x))) (.var .here)))) (max h.specs.length M) (by
        intro Ξ s av
        exact max_le_max_left _ (hk _ (fun x => .there (.there (s x))) (.var .here)))
      simpa [Term.emit,Term.sourceMax,max_assoc,max_left_comm] using hh
end LogicLineages.ControlSensitivityCurrent.SourceAST
