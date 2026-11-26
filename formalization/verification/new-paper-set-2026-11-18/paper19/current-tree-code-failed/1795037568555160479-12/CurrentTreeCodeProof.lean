module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeCode

open RawSourceDAG
open LogicLineages.OrdinalComparison.Source GroundEquivalence

private theorem index_eq {Γ τ} (v : Variable Γ τ) :
    RawSourceDAG.variableIndex v = SourceTypedPorts.variableIndex v := by
  induction v with
  | here => rfl
  | there x ih => simp only [RawSourceDAG.variableIndex, SourceTypedPorts.variableIndex, ih]

private theorem reference_eq {Γ ss} (d : DAG Γ ss) : ∀ {s} (r : Ref ss s),
    (table (encodeGraph d)).getD (referenceIndex r) 7 = SyntaxCode.encodeTerm (d.values r) := by
  induction d with
  | nil => intro s r; cases r
  | var d x ih =>
    intro s r
    cases r with
    | here =>
      change 8 * RawSourceDAG.variableIndex x = 8 * SourceTypedPorts.variableIndex x
      rw [index_eq]
    | there r => exact ih r
  | app d f a ih =>
    intro s r
    cases r with
    | here =>
      change 8 * Nat.pair ((table (encodeGraph d)).getD (referenceIndex f) 7)
        ((table (encodeGraph d)).getD (referenceIndex a) 7) + 5 =
        8 * Nat.pair (SyntaxCode.encodeTerm (d.values f)) (SyntaxCode.encodeTerm (d.values a)) + 5
      rw [ih f, ih a]
    | there r => exact ih r
  | lam d b ih =>
    intro s r
    cases r with
    | here =>
      change 8 * Nat.pair _ ((table (encodeGraph d)).getD (referenceIndex b) 7) + 6 =
        8 * Nat.pair _ (SyntaxCode.encodeTerm (d.values b)) + 6
      rw [ih b]
    | there r => exact ih r
  | zero d ih =>
    intro s r
    cases r with
    | here => rfl
    | there r => exact ih r
  | succ d ih =>
    intro s r
    cases r with
    | here => rfl
    | there r => exact ih r
  | case d τ ih =>
    intro s r
    cases r with
    | here => rfl
    | there r => exact ih r
  | recursor d τ ih =>
    intro s r
    cases r with
    | here => rfl
    | there r => exact ih r

theorem exactExpansion : CurrentTreeCodeTargets.Exact := by
  intro Γ τ d
  exact reference_eq d.graph d.root

private theorem node_primitive :
    Primrec (fun p : Node × List Nat => nodeCode p.1 p.2) := by
  let P := Node × List Nat
  have hp : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : P => p.1.2.2.1) := Primrec.fst.comp hp
  have ha : Primrec (fun p : P => p.1.2.2.2) := Primrec.snd.comp hp
  have harg (j : Nat) : Primrec (fun p : P => p.1.2.2.2.getD j 0) :=
    (Primrec.list_getD 0).comp ha (Primrec.const j)
  have href (j : Nat) : Primrec (fun p : P => p.2.getD (p.1.2.2.2.getD j 0) 7) :=
    (Primrec.list_getD 7).comp Primrec.snd (harg j)
  have base {u : P → Nat} (hu : Primrec u) (k : Nat) : Primrec (fun p => 8*u p+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) hu) (Primrec.const k)
  have app := base (Primrec₂.natPair.comp (href 1) (href 2)) 5
  have lam := base (Primrec₂.natPair.comp (harg 0) (href 2)) 6
  have guard (k : Nat) : PrimrecPred (fun p : P => p.1.2.2.1 = k) :=
    Primrec.eq.comp ht (Primrec.const k)
  have hv := Primrec.nat_mul.comp (Primrec.const 8) (harg 0)
  exact Primrec.ite (guard 0) hv (Primrec.ite (guard 1) app (Primrec.ite (guard 2) lam
    (Primrec.ite (guard 3) (Primrec.const 1) (Primrec.ite (guard 4) (Primrec.const 2)
      (Primrec.ite (guard 5) (base (harg 0) 3) (Primrec.ite (guard 6) (base (harg 0) 4) (Primrec.const 7)))))))

theorem effective : CurrentTreeCodeTargets.Effective := by
  have h := Primrec.list_cons.comp node_primitive Primrec.snd
  have hf : Primrec table :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (h.comp (Primrec.snd : Primrec (fun p : List Node × (Node × List Nat) => p.2))).to₂
  exact (Primrec.list_getD 7).comp
    (hf.comp (Primrec.fst.comp Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

end LogicLineages.ControlSensitivityCurrent.CurrentTreeCode
