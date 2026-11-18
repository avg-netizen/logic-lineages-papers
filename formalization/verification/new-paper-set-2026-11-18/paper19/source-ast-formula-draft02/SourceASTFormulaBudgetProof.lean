module
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaSemanticProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering

def BudgetSpec {Δ m} (k : BooleanContinuation Δ m) (K M : Nat) : Prop :=
  ∀ (Ξ : List Ty) (n : Nat) (s : Renaming Δ Ξ) (e : Fin m → Fin n) (root : Fin n),
    (k s e root).cost ≤ K ∧ (k s e root).sourceMax ≤ M

theorem relation_budgets {Γ Δ m} (a b : Term Γ) (r : Renaming Γ Δ)
    (node : ∀ {Ξ n}, Port Ξ → Port Ξ → InputNormalization.Node Ξ n)
    (k : BooleanContinuation Δ m) (K M : Nat) (hk : BudgetSpec k K M) :
    (emitRelation a b r node k).cost ≤ a.cost+b.cost+3+K ∧
    (emitRelation a b r node k).sourceMax ≤ max (max a.sourceMax b.sourceMax) M := by
  constructor
  · have ha := cost Γ Δ m r a (fun s av => b.emit (fun x => s (r x)) (fun t bv =>
        .boolean (node (ExistentialPlan.portRename t av) bv)
          (k (fun x => t (s x)) Fin.succ 0))) (b.cost+3+K) (by
      intro Ξ s av
      have hb := cost Γ Ξ m (fun x => s (r x)) b (fun t bv =>
        .boolean (node (ExistentialPlan.portRename t av) bv)
          (k (fun x => t (s x)) Fin.succ 0)) (3+K) (by
        intro Ω t bv
        exact Nat.add_le_add_left (hk Ω (m+1) (fun x => t (s x)) Fin.succ 0).1 3)
      simpa [Nat.add_assoc] using hb)
    simpa [emitRelation,Nat.add_assoc] using ha
  · have ha := sourceTables Γ Δ m r a (fun s av => b.emit (fun x => s (r x)) (fun t bv =>
        .boolean (node (ExistentialPlan.portRename t av) bv)
          (k (fun x => t (s x)) Fin.succ 0))) (max b.sourceMax M) (by
      intro Ξ s av
      exact sourceTables Γ Ξ m (fun x => s (r x)) b (fun t bv =>
        .boolean (node (ExistentialPlan.portRename t av) bv)
          (k (fun x => t (s x)) Fin.succ 0)) M (by
        intro Ω t bv
        exact (hk Ω (m+1) (fun x => t (s x)) Fin.succ 0).2))
    simpa [emitRelation,max_assoc] using ha

theorem formula_budgets {Γ} (a : Formula Γ) :
    ∀ {Δ m} (r : Renaming Γ Δ) (k : BooleanContinuation Δ m) (K M : Nat),
    BudgetSpec k K M →
    ((a.emit r k).cost ≤ a.cost+K ∧ (a.emit r k).sourceMax ≤ max a.sourceMax M) := by
  induction a with
  | truth =>
      intro Δ m r k K M hk
      have h := hk Δ (m+1) (fun x => x) Fin.succ 0
      exact ⟨Nat.add_le_add_left h.1 3,by simpa [Formula.emit,Formula.sourceMax,InputNormalization.Input.sourceMax] using h.2⟩
  | falsity =>
      intro Δ m r k K M hk
      have h := hk Δ (m+1) (fun x => x) Fin.succ 0
      exact ⟨Nat.add_le_add_left h.1 3,by simpa [Formula.emit,Formula.sourceMax,InputNormalization.Input.sourceMax] using h.2⟩
  | eq a b => intro Δ m r k K M hk; exact relation_budgets a b r (fun x y => .eq x y) k K M hk
  | le a b => intro Δ m r k K M hk; exact relation_budgets a b r (fun x y => .le x y) k K M hk
  | lt a b => intro Δ m r k K M hk; exact relation_budgets a b r (fun x y => .lt x y) k K M hk
  | neg a ih =>
      intro Δ m r k K M hk
      have h := ih r (fun s e root => .boolean (.neg root) (k s (fun i => (e i).succ) 0)) (3+K) M (by
        intro Ξ n s e root
        exact ⟨Nat.add_le_add_left (hk Ξ (n+1) s (fun i => (e i).succ) 0).1 3,
          (hk Ξ (n+1) s (fun i => (e i).succ) 0).2⟩)
      simpa [Formula.emit,Formula.cost,Formula.sourceMax,Nat.add_assoc] using h
  | conj a b iha ihb =>
      intro Δ m r k K M hk
      have h := iha r (fun s e left => b.emit (fun x => s (r x)) (fun t h right =>
        .boolean (.conj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)))
        (b.cost+3+K) (max b.sourceMax M) (by
        intro Ξ n s e left
        have hb := ihb (fun x => s (r x)) (fun t h right =>
          .boolean (.conj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)) (3+K) M (by
          intro Ω l t h right
          have hh := hk Ω (l+1) (fun x => t (s x)) (fun i => (h (e i)).succ) 0
          exact ⟨Nat.add_le_add_left hh.1 3,hh.2⟩)
        simpa [Nat.add_assoc] using hb)
      simpa [Formula.emit,Formula.cost,Formula.sourceMax,Nat.add_assoc,max_assoc] using h
  | disj a b iha ihb =>
      intro Δ m r k K M hk
      have h := iha r (fun s e left => b.emit (fun x => s (r x)) (fun t h right =>
        .boolean (.disj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)))
        (b.cost+3+K) (max b.sourceMax M) (by
        intro Ξ n s e left
        have hb := ihb (fun x => s (r x)) (fun t h right =>
          .boolean (.disj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)) (3+K) M (by
          intro Ω l t h right
          have hh := hk Ω (l+1) (fun x => t (s x)) (fun i => (h (e i)).succ) 0
          exact ⟨Nat.add_le_add_left hh.1 3,hh.2⟩)
        simpa [Nat.add_assoc] using hb)
      simpa [Formula.emit,Formula.cost,Formula.sourceMax,Nat.add_assoc,max_assoc] using h

theorem formulaBudgets : SourceASTFormulaTargets.Budgets := by
  intro Γ Δ m r a k K M hk
  exact formula_budgets a r k K M hk
end LogicLineages.ControlSensitivityCurrent.SourceAST
