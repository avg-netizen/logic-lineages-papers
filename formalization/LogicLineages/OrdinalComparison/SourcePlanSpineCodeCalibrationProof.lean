module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeEmbeddingProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeForestsProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof
open ExistentialPlan PrimitiveLowering SourcePrimitiveForestCode GroundEquivalence

theorem rename_code {Γ Δ} (k : Nat) (r : Renaming Γ Δ)
    (h : ∀ τ (x : Variable Γ τ),SourceTypedPorts.variableIndex (r x)=SourceTypedPorts.variableIndex x+k)
    (a : Input Γ .ground) :
    ContextInsertionCode.sourceCode 0 k (SyntaxCode.encodeTerm a.term)=
      SyntaxCode.encodeTerm (ScopedDAG.renameInput r a).term := by
  rw [(ScopedDAG.Proof.renaming Γ Δ .ground r a).1]
  exact SourcePlanPrefixCode.Proof.prefix_correct k r h a.term

theorem rename_pairs {Γ Δ} (k : Nat) (r : Renaming Γ Δ)
    (h : ∀ τ (x : Variable Γ τ),SourceTypedPorts.variableIndex (r x)=SourceTypedPorts.variableIndex x+k)
    (es : List (Input Γ .ground × Input Γ .ground)) :
    SourcePlanPrefixCode.shiftPairs k (es.map (fun p => (SyntaxCode.encodeTerm p.1.term,SyntaxCode.encodeTerm p.2.term))) =
    (es.map (fun p => (ScopedDAG.renameInput r p.1,ScopedDAG.renameInput r p.2))).map
      (fun p => (SyntaxCode.encodeTerm p.1.term,SyntaxCode.encodeTerm p.2.term)) := by
  simp only [SourcePlanPrefixCode.shiftPairs,List.map_map]
  apply List.map_congr_left
  intro p hp
  change (ContextInsertionCode.sourceCode 0 k (SyntaxCode.encodeTerm p.1.term),ContextInsertionCode.sourceCode 0 k (SyntaxCode.encodeTerm p.2.term)) = _
  rw [rename_code k r h,rename_code k r h]
  rfl

theorem embedding_port {Γ} (q : Plan Γ) (a : Port Γ) :
    shiftPort q.witnesses (portNumber a)=portNumber (portRename (compile q).embedding a) := by
  cases a with
  | zero => simp [shiftPort,portNumber,portRename]
  | var x =>
    simp only [portRename,portNumber,shiftPort,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false]
    rw [(SourcePlanPrefixCode.Proof.actualEmbedding Γ q).2]
    omega

theorem run_correct {Γ} (q : Plan Γ) (hq : ParametricExistentialPlan.Supported q) :
    run (spine q)=(q.witnesses,compiledPairs q) := by
  induction q with
  | done => rfl
  | @equation Γ a b q ih =>
    have h := ih hq
    change step (0,SyntaxCode.encodeTerm a.term,SyntaxCode.encodeTerm b.term,0) (run (spine q)) = _
    rw [h]
    simp only [step,ite_true]
    change (q.witnesses,(ContextInsertionCode.sourceCode 0 q.witnesses (SyntaxCode.encodeTerm a.term),ContextInsertionCode.sourceCode 0 q.witnesses (SyntaxCode.encodeTerm b.term))::compiledPairs q) = _
    rw [rename_code q.witnesses (compile q).embedding (SourcePlanPrefixCode.Proof.actualEmbedding Γ q).2,
      rename_code q.witnesses (compile q).embedding (SourcePlanPrefixCode.Proof.actualEmbedding Γ q).2]
    rfl
  | @gate Γ g q ih =>
    have h := ih hq.2
    have hs := rename_pairs 9 (shift (Γ:=(compile q).context) 9)
      (fun _ x => SourcePrimitiveForestCode.Proof.shift_index 9 x) (compile q).forest
    cases g with
    | eq a b =>
      change step (1,portNumber a,portNumber b,0) (run (spine q)) = _
      rw [h]
      simp only [step,show (1:Nat)≠0 by decide,ite_false,ite_true]
      rw [embedding_port,embedding_port,SourcePrimitiveForestCode.Proof.exactForests.1]
      simp only [compiledPairs,compile,Plan.witnesses,gateRename,forestCodes,List.map_append,hs]
    | add a b c =>
      change step (2,portNumber a,portNumber b,portNumber c) (run (spine q)) = _
      rw [h]
      simp only [step,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,ite_false,ite_true]
      rw [embedding_port,embedding_port,embedding_port,SourcePrimitiveForestCode.Proof.exactForests.2.1]
      simp only [compiledPairs,compile,Plan.witnesses,gateRename,forestCodes,List.map_append,hs]
    | one a =>
      change step (3,portNumber a,0,0) (run (spine q)) = _
      rw [h]
      simp only [step,show (3:Nat)≠0 by decide,show (3:Nat)≠1 by decide,show (3:Nat)≠2 by decide,ite_false,ite_true]
      rw [embedding_port,SourcePrimitiveForestCode.Proof.exactForests.2.2]
      simp only [compiledPairs,compile,Plan.witnesses,gateRename,forestCodes,List.map_append,hs]
    | sort a b c d => exact False.elim hq.1
  | existsGround q ih =>
    change step (4,0,0,0) (run (spine q)) = _
    rw [ih hq]
    rfl

theorem tags_supported {Γ} (q : Plan Γ) (hq : ParametricExistentialPlan.Supported q) : ∀ i ∈ spine q,i.1≤4 := by
  induction q with
  | done => simp [spine]
  | equation a b q ih => simpa [spine] using ih hq
  | gate g q ih =>
    have ht := ih hq.2
    cases g <;> simp_all [spine,gateInstruction,ParametricExistentialPlan.Supported,ParametricPrimitiveLowering.Supported]
    all_goals exact ht
  | existsGround q ih => simpa [spine] using ih hq

theorem exactCompilation : Targets.ExactCompilation := fun q hq => ⟨tags_supported q hq,run_correct q hq⟩
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof
