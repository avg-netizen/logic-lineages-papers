module
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentProbeCode

open LogicLineages.OrdinalComparison.Source GroundEquivalence GroundClosing
open RawSourceDAG CheckedComposition Operations

private theorem lookup_prefix (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = Ty.ground) (Δ : List Ty)
    {τ : Ty} (x : Variable (Δ++Γ) τ) :
    match AbsoluteProbeDAG.prefixMap (AbsoluteObserver.closingMap hg) Δ x with
    | .zero => Δ.length ≤ variableIndex x
    | .var y => variableIndex x < Δ.length ∧ variableIndex y = variableIndex x := by
  induction Δ with
  | nil =>
    have h := AbsoluteObserver.groundType hg x
    cases h
    change 0 ≤ variableIndex x
    exact Nat.zero_le _
  | cons σ Δ ih =>
    cases x with
    | here =>
      change 0 < Δ.length+1 ∧ 0 = 0
      exact ⟨Nat.zero_lt_succ _,rfl⟩
    | there x =>
      have hx := ih x
      simp only [AbsoluteProbeDAG.prefixMap, GroundMap.lift, List.length_cons, variableIndex]
      cases h : AbsoluteProbeDAG.prefixMap (AbsoluteObserver.closingMap hg) Δ x with
      | var y =>
        rw [h] at hx
        exact ⟨Nat.succ_lt_succ hx.1,congrArg (·+1) hx.2⟩
      | zero =>
        rw [h] at hx
        exact Nat.succ_le_succ hx

private theorem closed_table (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = Ty.ground) {ss} (d : DAG Γ ss) :
    encodeGraph (AbsoluteProbeDAG.mapGraph (AbsoluteObserver.closingMap hg) d) =
      (encodeGraph d).map closeNode := by
  induction d with
  | nil => rfl
  | @var ss Δ τ d x ih =>
    have hx := lookup_prefix Γ hg Δ x
    simp only [AbsoluteProbeDAG.mapGraph, encodeGraph, List.map_cons]
    cases h : AbsoluteProbeDAG.prefixMap (AbsoluteObserver.closingMap hg) Δ x with
    | var y =>
      rw [h] at hx
      simp [encodeGraph, ih, node, closeNode, hx.2, Nat.not_le_of_gt hx.1]
    | zero =>
      rw [h] at hx
      simp [encodeGraph, ih, node, closeNode, hx, SyntaxCode.typeCode]
  | app d f a ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]
  | lam d b ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]
  | zero d ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]
  | succ d ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]
  | case d τ ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]
  | recursor d τ ih => simp [AbsoluteProbeDAG.mapGraph, encodeGraph, ih, node, closeNode]

theorem exactClosing : CurrentProbeCodeTargets.ExactClosing := by
  intro Γ τ hg d
  unfold closeRaw encode AbsoluteProbeDAG.closeInput AbsoluteProbeDAG.mapInput
  rw [closed_table Γ hg d.graph]
  rfl

theorem exactProbe : CurrentProbeCodeTargets.ExactProbe := by
  intro Γ τ d x
  simp only [probeRaw, encode, AbsoluteProbeDAG.probeInput, encodeGraph, referenceIndex,
    rawNode, node, SyntaxCode.typeCode, List.map_cons, List.map_nil, insert_graph]
  rw [map_index]
  rfl

private theorem closeNode_primitive : Primrec closeNode := by
  have hprefix := Primrec.list_length.comp (Primrec.fst : Primrec fun a : Node => a.1)
  have htag := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd : Primrec fun a : Node => a.2))
  have hargs := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd : Primrec fun a : Node => a.2))
  have hidx := (Primrec.list_getD 0).comp hargs (Primrec.const 0)
  have hz : Primrec (fun a : Node => ((a.1,0,3,[]) : Node)) :=
    Primrec.fst.pair (Primrec.const (0,3,[]))
  exact Primrec.ite ((Primrec.eq.comp htag (Primrec.const 0)).and (Primrec.nat_le.comp hprefix hidx)) hz Primrec.id

private theorem close_primitive : Primrec closeRaw := by
  have ht : Primrec (fun d : Code => d.2.1.map closeNode) :=
    Primrec.list_map (Primrec.fst.comp Primrec.snd) (closeNode_primitive.comp Primrec.snd).to₂
  exact (Primrec.const []).pair (ht.pair (Primrec.snd.comp Primrec.snd))

private theorem probe_primitive : Primrec₂ probeRaw := by
  let P := Code × Nat
  have hc : Primrec (fun q : P => q.1) := Primrec.fst
  have hΓ : Primrec (fun q : P => q.1.1) := Primrec.fst.comp hc
  have ht : Primrec (fun q : P => q.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hr : Primrec (fun q : P => q.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have htail := insert_table_primitive.comp (Primrec.fst.comp (Primrec.snd.comp hc))
  have hArrow : Primrec₂ SyntaxCode.arrowCode := by
    unfold SyntaxCode.arrowCode
    exact Primrec.nat_add.comp (Primrec₂.natPair) (Primrec.const 1)
  have nodeP (ty : P → Nat) (hy : Primrec ty) (tag : Nat)
      (args : P → List Nat) (ha : Primrec args) :
      Primrec (fun q => rawNode (ty q) tag (args q)) :=
    (Primrec.const []).pair (hy.pair ((Primrec.const tag).pair ha))
  have one {g : P → Nat} (h : Primrec g) : Primrec (fun p => [g p]) :=
    Primrec.list_cons.comp h (Primrec.const [])
  have h1 := nodeP _ (Primrec.const 0) 1 _ (Primrec.list_cons.comp ht (Primrec.const [0,2]))
  have h2 := nodeP _ (hArrow.comp ht (Primrec.const 0)) 2 _ (Primrec.list_cons.comp ht (Primrec.const [0,0]))
  have h3 : Primrec (fun q : P => (([q.1.2.2.2],0,3,[]) : Node)) :=
    (one ht).pair (Primrec.const (0,3,[]))
  have h4 := nodeP _ ht 1 _ (Primrec.const [0,1,0])
  have h5 := nodeP _ (Primrec.const 0) 0 _ (one (Primrec.snd : Primrec (fun q : P => q.2)))
  have h6 := nodeP _ (hArrow.comp (Primrec.const 0) ht) 2 _
    (Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp ht (one hr)))
  have body := Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.list_cons.comp h3
    (Primrec.list_cons.comp h4 (Primrec.list_cons.comp h5 (Primrec.list_cons.comp h6 htail)))))
  exact hΓ.pair (body.pair (Primrec.const (0,0)))

theorem effective : CurrentProbeCodeTargets.Effective := ⟨close_primitive, probe_primitive⟩

end LogicLineages.ControlSensitivityCurrent.CurrentProbeCode
