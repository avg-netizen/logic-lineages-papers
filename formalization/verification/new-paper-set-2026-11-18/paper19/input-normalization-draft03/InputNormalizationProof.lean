module
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.InputNormalization
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering

theorem portRename_value {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (σ : Variable Δ .ground → Nat)
    (h : ∀ x, σ (r x)=ρ x) (a : Port Γ) :
    (ExistentialPlan.portRename r a).value (ExistentialPlan.inputs σ) =
      a.value (ExistentialPlan.inputs ρ) := by
  cases a with
  | zero => rfl
  | var x => exact h x

theorem node_naturality {Γ Δ m} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (σ : Variable Δ .ground → Nat)
    (h : ∀ x, σ (r x)=ρ x) (v : Fin m → Bool) (a : Node Γ m) :
    (a.rename r).eval σ v = a.eval ρ v := by
  cases a <;> simp only [Node.rename,Node.eval,portRename_value r ρ σ h]

theorem referenceNaturality : InputNormalizationTargets.ReferenceNaturality := by
  intro Γ Δ r ρ σ h m d
  induction d with
  | nil => rfl
  | snoc d n ih => simp only [Dag.rename,Dag.eval,ih,node_naturality r ρ σ h]

theorem mapNode_eval {n k m} (r : Fin n → Fin k) (a : Fin k → Nat)
    (v : Fin m → Bool) (node : BooleanWire.Node n m) :
    BooleanWire.evalNode a v (mapNode r node) = BooleanWire.evalNode (fun i => a (r i)) v node := by
  cases node <;> rfl

theorem mapDag_eval {n k m} (r : Fin n → Fin k) (a : Fin k → Nat)
    (d : BooleanWire.Dag n m) :
    BooleanWire.evaluate (mapDag r d) a = BooleanWire.evaluate d (fun i => a (r i)) := by
  induction d with
  | nil => rfl
  | snoc d node ih => simp only [mapDag,BooleanWire.evaluate,ih,mapNode_eval]

theorem node_wire {Γ m} (ρ : Variable Γ .ground → Nat) (d : Dag Γ m)
    (v : Fin m → Bool) (n : Node Γ m) :
    BooleanWire.evalNode (fun i => ((Dag.snoc d n).ports i).value (ExistentialPlan.inputs ρ)) v n.wire =
      n.eval ρ v := by
  cases n <;> simp [Node.wire,Node.eval,BooleanWire.evalNode,Dag.ports,Node.ports] <;> rfl

theorem wireCorrect : InputNormalizationTargets.WireCorrect := by
  intro Γ ρ m d
  induction d with
  | nil => rfl
  | snoc d n ih =>
      have hh : BooleanWire.evaluate (mapDag (Fin.castAdd 2) d.wires)
          (fun i => ((Dag.snoc d n).ports i).value (ExistentialPlan.inputs ρ)) = d.eval ρ := by
        rw [mapDag_eval]
        simpa [Dag.ports] using ih
      simp only [Dag.wires,BooleanWire.evaluate]
      simp only [arity] at *
      rw [hh, node_wire]
      rfl

theorem weaken_eval {Γ m} (ρ : Variable Γ .ground → Nat) (n : Nat) (d : Dag Γ m) :
    (d.rename (Renaming.weaken Γ .ground)).eval (ExistentialPlan.extend ρ n) = d.eval ρ :=
  referenceNaturality Γ (.ground::Γ) (Renaming.weaken Γ .ground) ρ
    (ExistentialPlan.extend ρ n) (fun _ => rfl) m d

theorem normalization : InputNormalizationTargets.Normalization := by
  intro p f Γ ρ m d q
  induction q with
  | finish root =>
      simp only [normalize,programEval,Input.eval]
      rw [wireCorrect _ _ _ _]
  | boolean n q ih =>
      exact ih ρ (.snoc d n)
  | add a b q ih =>
      simp only [normalize,programEval,Input.eval]
      rw [ih, weaken_eval]
  | literal k q ih =>
      simp only [normalize,programEval,Input.eval]
      rw [ih, weaken_eval]
  | observation t q ih =>
      simp only [normalize,programEval,Input.eval]
      rw [ih, weaken_eval]
  | unary h x q ih =>
      simp only [normalize,programEval,Input.eval]
      rw [ih, weaken_eval]

theorem arity_eq (m : Nat) : arity m = 2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [arity,ih,Nat.mul_add]

theorem codeSize_eq {Γ m} (d : Dag Γ m) (q : Input Γ m) :
    (normalize d q).codeSize = q.cost+3*m := by
  induction q with
  | finish root => simp [normalize,BooleanCompiler.Program.codeSize,Input.cost,arity_eq]; omega
  | boolean n q ih => simp only [normalize,Input.cost]; rw [ih]; omega
  | add a b q ih => simp only [normalize,BooleanCompiler.Program.codeSize,Input.cost]; rw [ih]; omega
  | literal k q ih => simp only [normalize,BooleanCompiler.Program.codeSize,Input.cost]; rw [ih]; omega
  | observation t q ih => simp only [normalize,BooleanCompiler.Program.codeSize,Input.cost]; rw [ih]; omega
  | unary h x q ih => simp only [normalize,BooleanCompiler.Program.codeSize,Input.cost]; rw [ih]; omega

theorem sourceMax_eq {Γ m} (d : Dag Γ m) (q : Input Γ m) :
    (normalize d q).sourceMax = q.sourceMax := by
  induction q with
  | finish root => rfl
  | boolean n q ih => exact ih (.snoc d n)
  | add a b q ih => exact ih _
  | literal k q ih => exact ih _
  | observation t q ih => simp only [normalize,BooleanCompiler.Program.sourceMax,Input.sourceMax,ih]
  | unary h x q ih => simp only [normalize,BooleanCompiler.Program.sourceMax,Input.sourceMax,ih]

-- Structural load induction reproduced from SourceBooleanCompilerSizeProof.load_bound;
-- no semantic fixed-control proof dependency is imported.
theorem program_load_le {Γ} (p : BooleanCompiler.Program Γ) :
    p.load ≤ p.codeSize*(p.sourceMax+1) := by
  induction p with
  | matrix d a root => simp [BooleanCompiler.Program.load,BooleanCompiler.Program.codeSize,BooleanCompiler.Program.sourceMax]
  | add a b q ih =>
      simp only [BooleanCompiler.Program.load,BooleanCompiler.Program.codeSize,BooleanCompiler.Program.sourceMax,Nat.add_mul,Nat.one_mul]
      omega
  | literal k q ih =>
      have hb : (Nat.log2 k+2)*1 ≤ (Nat.log2 k+2)*(q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Nat.add_mul,Nat.mul_one] at hb
      simp only [BooleanCompiler.Program.load,BooleanCompiler.Program.codeSize,BooleanCompiler.Program.sourceMax,Nat.add_mul]
      omega
  | observation t q ih =>
      have ht := Nat.le_max_left t.specs.length q.sourceMax
      have hq := Nat.le_max_right t.specs.length q.sourceMax
      have hm : q.codeSize*(q.sourceMax+1) ≤ q.codeSize*(max t.specs.length q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [BooleanCompiler.Program.load,BooleanCompiler.Program.codeSize,BooleanCompiler.Program.sourceMax,Nat.add_mul,Nat.one_mul]
      omega
  | unary h x q ih =>
      have ht := Nat.le_max_left h.specs.length q.sourceMax
      have hq := Nat.le_max_right h.specs.length q.sourceMax
      have hm : q.codeSize*(q.sourceMax+1) ≤ q.codeSize*(max h.specs.length q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [BooleanCompiler.Program.load,BooleanCompiler.Program.codeSize,BooleanCompiler.Program.sourceMax,Nat.add_mul]
      omega

theorem budgets : InputNormalizationTargets.Budgets := by
  intro Γ m d q
  exact ⟨codeSize_eq d q,sourceMax_eq d q,by
    simpa only [codeSize_eq,sourceMax_eq] using program_load_le (normalize d q)⟩
end LogicLineages.ControlSensitivityCurrent.InputNormalization
