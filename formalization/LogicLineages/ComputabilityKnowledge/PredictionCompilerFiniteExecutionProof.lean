module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableProof
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionProof
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerFiniteTable PredictionCompilerFiniteExecution
open PredictionCompilerFiniteExecutionTargets

private theorem numeric_at {q a : Nat} (m : PredictionFiniteSerialization.FinMachine q a)
    (x : TM0.Cfg (Fin (a + 3)) (Fin (q + 1)))
    (next : Option (TM0.Cfg (Fin (a + 3)) (Fin (q + 1))))
    (h : PredictionCompilerFiniteTableTargets.NumericStepAt m x next) :
    tableStep m (PredictionFiniteSerialization.embedCfg x) =
      next.map PredictionFiniteSerialization.embedCfg := h

private theorem numeric_step (c : Code) (k : Cont') (x : TM0.Cfg TapeAlphabet PostLabel)
    (hx : x.q ∈ postLabels c k) :
    tableStep (finiteData c k) (numericCfg c k x) =
      (TM0.step postMachine x).map (numericCfg c k) := by
  have h := numeric_at (finiteData c k) (finiteCfg c k x)
    ((TM0.step postMachine x).map (finiteCfg c k))
    (PredictionCompilerFiniteTableProof.exactNumericStep c k x hx)
  simp only [Option.map_map, Function.comp_def] at h
  have hn : (fun y : TM0.Cfg TapeAlphabet PostLabel =>
      PredictionFiniteSerialization.embedCfg (finiteCfg c k y)) = numericCfg c k := by
    funext y
    rfl
  exact h.trans (congrArg (fun f => (TM0.step postMachine x).map f) hn)

private theorem respects_of_map {α β : Type} (f : α → Option α) (g : β → Option β)
    (h : α → β) (S : α → Prop)
    (closed : ∀ x y, f x = some y → S x → S y)
    (step : ∀ x, S x → g (h x) = (f x).map h) :
    StateTransition.Respects f g (fun x d => S x ∧ h x = d) := by
  intro x _ hx
  obtain ⟨hx, rfl⟩ := hx
  cases he : f x with
  | none => rw [step x hx, he]; rfl
  | some y =>
    refine ⟨h y, ⟨closed x y he hx, rfl⟩, Relation.TransGen.single ?_⟩
    rw [step x hx, he]
    rfl

theorem exactReachableSimulation : ExactReachableSimulation := by
  intro c k
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  apply respects_of_map (TM0.step postMachine) (tableStep (finiteData c k))
    (numericCfg c k) (fun x => x.q ∈ postLabels c k)
  · intro x y he hx
    exact TM0.step_supports postMachine
      (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c k) he hx
  · exact numeric_step c k

private theorem initial_stack (c : Code) (v : List Nat) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    TM2to1.TrCfg (PartrecToTM2.init c v)
      (TM1.init (sourceInput v) : TM1.Cfg TapeAlphabet TapeLabel Store) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have h := TM2to1.trCfg_init (Γ := StackAlphabet) (Λ := Λ') (σ := Store) K'.main (trList v)
  convert h using 1 <;> try rfl
  apply congrArg (fun s => (⟨some (trNormal c Cont'.halt), none, s⟩ : PartrecToTM2.Cfg'))
  funext j
  cases j <;> simp [K'.elim, Function.update]

private theorem initial_support (c : Code) (v : List Nat) :
    (sourceInit c v).q ∈ postLabels c Cont'.halt := by
  exact (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).1

theorem forwardEncodedOutput : ForwardEncodedOutput := by
  intro c v w hw
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : PartrecToTM2.halt w ∈
      StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact Part.mem_map _ hw
  obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval (TM2to1.tr_respects tr) (initial_stack c v) hs
  obtain ⟨y, hy, hey⟩ := StateTransition.tr_eval (TM1to0.tr_respects tapeMachine) rfl hex
  obtain ⟨d, hd, hed⟩ := StateTransition.tr_eval (exactReachableSimulation c Cont'.halt)
    (show (sourceInit c v).q ∈ postLabels c Cont'.halt ∧
      numericCfg c Cont'.halt (sourceInit c v) = numericCfg c Cont'.halt (sourceInit c v)
      from ⟨initial_support c v, rfl⟩) hey
  refine ⟨d, hed, x, hx, ?_⟩
  rw [hy]
  exact hd.2

theorem reverseEncodedOutput : ReverseEncodedOutput := by
  intro c v d hd
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  obtain ⟨y, hy, hey⟩ := StateTransition.tr_eval_rev (exactReachableSimulation c Cont'.halt)
    (show (sourceInit c v).q ∈ postLabels c Cont'.halt ∧
      numericCfg c Cont'.halt (sourceInit c v) = numericCfg c Cont'.halt (sourceInit c v)
      from ⟨initial_support c v, rfl⟩) hd
  obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval_rev (TM1to0.tr_respects tapeMachine)
    (show TM1to0.trCfg tapeMachine
      (TM1.init (sourceInput v) : TM1.Cfg TapeAlphabet TapeLabel Store) = sourceInit c v from rfl) hey
  obtain ⟨z, hz, hez⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects tr) (initial_stack c v) hex
  rw [PartrecToTM2.tr_eval] at hez
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).1 hez
  refine ⟨w, hw, x, hz, ?_⟩
  rw [hx]
  exact hy.2

theorem exactTermination : ExactTermination := by
  intro c v
  constructor
  · intro h
    obtain ⟨w, hw, _⟩ := reverseEncodedOutput c v _ ⟨h, rfl⟩
    exact hw.1
  · intro h
    obtain ⟨d, hd, _⟩ := forwardEncodedOutput c v _ ⟨h, rfl⟩
    exact hd.1

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionProof
