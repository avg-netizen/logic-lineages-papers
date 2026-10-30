module

public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryTargets
public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryProof
public import Mathlib.Data.List.GetD

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryProof
open PredictionGame PredictionLearning PredictionSelfHistory PredictionUniformHistory PredictionUniformHistoryTargets

private theorem fold_prefix {α β : Type} (xs : List α) (default : α) (step : β → α → β) (init : β)
    (n : Nat) (hn : n ≤ xs.length) :
    Nat.rec init (fun i prev => step prev (xs.getD i default)) n = (xs.take n).foldl step init := by
  induction n with
  | zero => simp
  | succ n ih =>
    change step (Nat.rec init (fun i prev => step prev (xs.getD i default)) n) (xs.getD n default) = _
    rw [ih (by omega), List.take_succ_eq_append_getElem (by omega),
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.getD_eq_getElem xs default (by omega)]

theorem uniformReconstructionComputable : UniformReconstructionComputable := by
  intro R hR
  have hr : Computable (fun q : (Nat × List Bool) × (Nat × (List Bool × List Bool)) =>
      R q.1.1 q.2.2.1 q.2.2.2) :=
    hR.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hx : Computable (fun q : (Nat × List Bool) × (Nat × (List Bool × List Bool)) =>
      q.1.2.getD q.2.1 false) :=
    (Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun q : Nat × List Bool => fun v : Nat × (List Bool × List Bool) =>
      reconstructStep (R q.1) v.2 (q.2.getD v.1 false)) := by
    have h := (Computable.list_concat.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)) hx).pair
      (Computable.list_concat.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) hr)
    apply h.to₂.of_eq
    intro q
    rfl
  have hrec := Computable.nat_rec (Computable.list_length.comp Computable.snd)
    (Computable.const (([], []) : List Bool × List Bool)) hstep
  apply hrec.of_eq
  intro q
  change Nat.rec (motive := fun _ => List Bool × List Bool) (([], []) : List Bool × List Bool) (fun i prev => reconstructStep (R q.1) prev (q.2.getD i false)) q.2.length = _
  rw [fold_prefix q.2 false (reconstructStep (R q.1)) ([], []) q.2.length le_rfl]
  simp only [List.take_length, reconstruct]

theorem uniformSelfPolicyComputable : UniformSelfPolicyComputable := by
  intro R hR
  have harg : Computable (fun q : Nat × List Bool => (q.1, q.2, (reconstruct (R q.1) q.2).2)) :=
    Computable.fst.pair (Computable.snd.pair (Computable.snd.comp (uniformReconstructionComputable R hR)))
  apply (hR.comp harg).of_eq
  intro q
  rfl

private theorem compiler_computable (u : Code) : Computable (compileSelfHistory u) :=
  (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id).to_comp

theorem uniformSelfHistoryProgram : UniformSelfHistoryProgram := by
  intro R hR
  let f : Nat → Nat := fun n => bitValue
    (selfPolicy (R n.unpair.1) ((Encodable.decode (α := List Bool) n.unpair.2).getD []))
  have hdecode : Computable (fun n : Nat => ((Encodable.decode (α := List Bool) n.unpair.2).getD [])) :=
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])).to_comp
  have harg : Computable (fun n : Nat => (n.unpair.1, ((Encodable.decode (α := List Bool) n.unpair.2).getD []))) :=
    (Computable.fst.comp Computable.unpair).pair hdecode
  have hpolicy := (uniformSelfPolicyComputable R hR).comp harg
  have hf : Computable f := by
    apply ((Primrec.dom_bool bitValue).to_comp.comp hpolicy).of_eq
    intro n
    rfl
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  have hsem : ∀ z : Nat, ∀ xs : List Bool,
      Nat.Partrec.Code.eval u (Nat.pair z (Encodable.encode xs)) = Part.some (bitValue (selfPolicy (R z) xs)) := by
    intro z xs
    rw [hu]
    change Part.some (f (Nat.pair z (Encodable.encode xs))) = _
    simp only [f, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  refine ⟨u, compiler_computable u, hsem, ?_⟩
  intro z
  have hs : ∀ xs : List Bool, Nat.Partrec.Code.eval (compileSelfHistory u z) (Encodable.encode xs) =
      Part.some (bitValue (selfPolicy (R z) xs)) := by
    intro xs
    rw [compileSelfHistory, Nat.Partrec.Code.eval_curry, hsem]
  have ht : TotalBinary (compileSelfHistory u z) := by
    intro xs
    refine ⟨selfPolicy (R z) xs, ?_⟩
    rw [hs]
    exact Part.mem_some_iff.mpr rfl
  refine ⟨hs, ht, ?_⟩
  funext xs
  have hv := Classical.choose_spec (ht xs)
  have hv' : bitValue (policy (compileSelfHistory u z) ht xs) ∈ Part.some (bitValue (selfPolicy (R z) xs)) :=
    Eq.mp (congrArg (fun v : Part Nat => bitValue (policy (compileSelfHistory u z) ht xs) ∈ v) (hs xs)) hv
  have heq := Part.mem_some_iff.mp hv'
  change bitValue (policy (compileSelfHistory u z) ht xs) = bitValue (selfPolicy (R z) xs) at heq
  cases ha : policy (compileSelfHistory u z) ht xs <;> cases hb : selfPolicy (R z) xs <;> simp_all [bitValue]

theorem uniformSelfHistoryPlay : UniformSelfHistoryPlay := by
  intro R hR
  obtain ⟨u, hu, _, hsem⟩ := uniformSelfHistoryProgram R hR
  refine ⟨u, hu, ?_⟩
  intro z
  obtain ⟨_, hp, heq⟩ := hsem z
  refine ⟨hp, ?_⟩
  intro e n
  dsimp only
  rw [heq]
  exact PredictionSelfHistoryProof.actualHistoryCalibration (R z) e n

end LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryProof
