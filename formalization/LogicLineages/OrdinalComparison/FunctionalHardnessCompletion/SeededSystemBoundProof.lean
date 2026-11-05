module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Proof
open OriginalDomain FunctionalDetector SourceCollisionCompletion SourceClasses SourceTypeSupport
open SeededCompiler.Proof (leaf_bound app_bound lam_bound rename_bound monotone_bound combine_bound)

private theorem zero_bound {Γ} : InternalLevelBound 3 (.zeroC : OriginalTerm Γ .ground) :=
  leaf_bound _ (by simp [typeSupport]) (by decide)

private theorem eraser_bound {Γ} (a b : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 3 a) (hb : InternalLevelBound 3 b) : InternalLevelBound 3 (eraser a b) := by
  apply app_bound _ _ (by decide) _ hb
  exact lam_bound _ (by decide) (rename_bound a _ ha)

private theorem ground_detector_bound {Γ} (a b : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 3 a) (hb : InternalLevelBound 3 b) :
    InternalLevelBound 3 (detectorLeft a b) ∧ InternalLevelBound 3 (detectorRight a b) :=
  ⟨eraser_bound _ _ (eraser_bound _ _ ha ha) (eraser_bound _ _ hb hb),
   eraser_bound _ _ (eraser_bound _ _ ha hb) (eraser_bound _ _ hb ha)⟩

private theorem pad_bound {Γ} (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 3 a) (hq : InternalLevelBound 3 q) : InternalLevelBound 3 (pad a q) := by
  apply app_bound _ _ (by decide) _ hq
  exact lam_bound _ (by decide) (rename_bound a _ ha)

private theorem aligned_bound {Γ} (a : OriginalTerm Γ unary) (ha : InternalLevelBound 3 a) :
    InternalLevelBound 3 (alignedLeft a) ∧ InternalLevelBound 3 (alignedRight a) := by
  have har := rename_bound a (shiftTwo Γ) ha
  exact ⟨pad_bound _ _ har (leaf_bound _ (by simp [typeSupport]) (by decide)),
    pad_bound _ _ har (leaf_bound _ (by simp [typeSupport]) (by decide))⟩

private theorem payload_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 3 a) (hb : InternalLevelBound 3 b) : InternalLevelBound 3 (payload a b) := by
  apply app_bound _ _ (by decide) (combine_bound _ _ hb ha)
  apply app_bound _ _ (by decide) (combine_bound _ _ ha hb)
  apply app_bound _ _ (by decide) (combine_bound _ _ hb hb)
  exact app_bound _ _ (by decide) (combine_bound _ _ ha ha) zero_bound

private theorem functional_detector_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 3 a) (hb : InternalLevelBound 3 b) :
    InternalLevelBound 3 (left a b) ∧ InternalLevelBound 3 (right a b) := by
  have hq := payload_bound a b ha hb
  exact ⟨eraser_bound _ _
      (app_bound _ _ (by decide) (combine_bound _ _ ha ha) hq)
      (app_bound _ _ (by decide) (combine_bound _ _ hb hb) hq),
    eraser_bound _ _
      (app_bound _ _ (by decide) (combine_bound _ _ ha hb) hq)
      (app_bound _ _ (by decide) (combine_bound _ _ hb ha) hq)⟩

private theorem aggregate_bound {Γ} (ps : List (OriginalTerm Γ .ground×OriginalTerm Γ .ground))
    (hp : ∀p∈ps,InternalLevelBound 3 p.1∧InternalLevelBound 3 p.2) :
    InternalLevelBound 3 (SourceAggregateCompletion.aggregate ps).1 ∧
      InternalLevelBound 3 (SourceAggregateCompletion.aggregate ps).2 := by
  induction ps with
  | nil => exact ⟨zero_bound,zero_bound⟩
  | cons p ps ih =>
      have hpair := hp p List.mem_cons_self
      have ht := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      have hd := ground_detector_bound p.1 p.2 hpair.1 hpair.2
      exact ⟨eraser_bound _ _ hd.1 ht.1,eraser_bound _ _ hd.2 ht.2⟩

private theorem detectors_bound {n : Nat} (s : System n) :
    ∀p∈(compile s).detectors,InternalLevelBound 3 p.1∧InternalLevelBound 3 p.2 := by
  induction s with
  | nil => intro p hp; exact False.elim (List.not_mem_nil hp)
  | cons d ds ih =>
      intro p hp
      have hc := SeededCompiler.Proof.compiler_bound (SeededCompiler.subtractSeed d)
      have ha := rename_bound _ (compile ds).original hc.1
      have hb := rename_bound _ (compile ds).original hc.2
      simp only [compile] at hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        exact functional_detector_bound _ _ (aligned_bound _ ha).1 (aligned_bound _ hb).2
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        have ht := ih q hq
        exact ⟨rename_bound _ _ ht.1,rename_bound _ _ ht.2⟩

private theorem context_bound {n : Nat} (s : System n) : ∀τ∈(compile s).context,τ.level≤1 := by
  induction s with
  | nil =>
      intro τ hτ
      simp only [compile,SignedPair.Context,List.mem_replicate] at hτ
      obtain ⟨_,rfl⟩ := hτ
      decide
  | cons d ds ih =>
      intro τ hτ
      simp only [compile,List.mem_cons] at hτ
      rcases hτ with rfl | rfl | hτ
      · decide
      · decide
      · exact ih τ hτ

theorem exactLevelThreeBounds : Targets.ExactLevelThreeBounds := by
  intro n s
  have hs := aggregate_bound (compile s).detectors (detectors_bound s)
  have hi : InternalLevelBound 3 (@GroundEquivalence.identity (compile s).context) :=
    monotone_bound _ SignedPair.Proof.identity_bound
  have hc : InternalLevelBound 3 (@GroundEquivalence.constant (compile s).context) :=
    lam_bound _ (by decide) zero_bound
  exact ⟨context_bound s,hs.1,hs.2,
    app_bound _ _ (by decide) hc hs.2,app_bound _ _ (by decide) hi hs.1⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Proof
