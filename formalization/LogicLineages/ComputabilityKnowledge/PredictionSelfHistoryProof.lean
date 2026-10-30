module

public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryProof
open PredictionGame PredictionLearning PredictionSelfHistory PredictionSelfHistoryTargets

private theorem reconstruct_snoc (R : PairedRule) (xs : List Bool) (x : Bool) :
    reconstruct R (xs ++ [x]) = reconstructStep R (reconstruct R xs) x := by
  simp [reconstruct]

theorem reconstructionLengths : ReconstructionLengths := by
  intro R xs
  induction xs using List.reverseRecOn with
  | nil => simp [reconstruct]
  | append_singleton xs x ih =>
      rw [reconstruct_snoc]
      simp [reconstructStep, ih.1, ih.2]

theorem reconstructionAppend : ReconstructionAppend := by
  intro R xs x
  rw [reconstruct_snoc]
  simp [reconstructStep, (reconstructionLengths R xs).1, selfPolicy]

private theorem game_reconstruction (R : PairedRule) (e : Policy) (n : Nat) :
    ((histories (selfPolicy R) e n).evasions, (histories (selfPolicy R) e n).predictions) =
      reconstruct R (histories (selfPolicy R) e n).evasions := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ihp := congrArg Prod.snd ih
      change ((histories (selfPolicy R) e n).evasions ++ [e (histories (selfPolicy R) e n).predictions],
        (histories (selfPolicy R) e n).predictions ++ [selfPolicy R (histories (selfPolicy R) e n).evasions]) =
        reconstruct R ((histories (selfPolicy R) e n).evasions ++ [e (histories (selfPolicy R) e n).predictions])
      rw [reconstructionAppend R]
      exact congrArg (fun ys => ((histories (selfPolicy R) e n).evasions ++
        [e (histories (selfPolicy R) e n).predictions], ys ++
        [selfPolicy R (histories (selfPolicy R) e n).evasions])) ihp

theorem actualHistoryCalibration : ActualHistoryCalibration := by
  intro R e n h
  have hh := game_reconstruction R e n
  refine ⟨hh, ?_⟩
  have hp := congrArg Prod.snd hh
  change R h.evasions (reconstruct R h.evasions).2 = R h.evasions h.predictions
  exact congrArg (R h.evasions) hp.symm

private theorem pr_reconstruct (R : PairedRule) (hR : Primrec₂ R) : Primrec (reconstruct R) := by
  have hs : Primrec (fun z : (List Bool × List Bool) × Bool => reconstructStep R z.1 z.2) :=
    ((Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
      (Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst)
        (hR.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))))
  exact Primrec.list_foldl Primrec.id (Primrec.const ([], [])) (hs.comp Primrec.snd).to₂

theorem primitiveRecursiveSelfPolicy : PrimitiveRecursiveSelfPolicy := by
  intro R hR
  exact hR.comp Primrec.id (Primrec.snd.comp (pr_reconstruct R hR))

theorem ordinarySelfPolicyProgram : OrdinarySelfPolicyProgram := by
  intro R hR
  let f : Nat → Nat := fun n => bitValue (selfPolicy R ((Encodable.decode (α := List Bool) n).getD []))
  have hf : Primrec f :=
    (Primrec.dom_bool bitValue).comp ((primitiveRecursiveSelfPolicy R hR).comp
      (Primrec.option_getD.comp Primrec.decode (Primrec.const [])))
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.to_comp)
  have hsem : ∀ xs, Nat.Partrec.Code.eval p (Encodable.encode xs) =
      Part.some (bitValue (selfPolicy R xs)) := by
    intro xs
    rw [hp]
    change Part.some (f (Encodable.encode xs)) = _
    simp only [f, Encodable.encodek, Option.getD_some]
  have htotal : TotalBinary p := by
    intro xs
    refine ⟨selfPolicy R xs, ?_⟩
    rw [hsem]
    exact Part.mem_some_iff.mpr rfl
  refine ⟨p, htotal, ?_⟩
  funext xs
  have hv := Classical.choose_spec (htotal xs)
  have hv' : bitValue (policy p htotal xs) ∈ Part.some (bitValue (selfPolicy R xs)) :=
    Eq.mp (congrArg (fun v : Part Nat => bitValue (policy p htotal xs) ∈ v) (hsem xs)) hv
  have heq := Part.mem_some_iff.mp hv'
  change bitValue (policy p htotal xs) = bitValue (selfPolicy R xs) at heq
  cases ha : policy p htotal xs <;> cases hb : selfPolicy R xs <;> simp_all [bitValue]

end LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryProof
