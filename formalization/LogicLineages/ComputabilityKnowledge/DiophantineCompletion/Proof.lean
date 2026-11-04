module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Proof
open Dioph DiophantineCompletion Targets

theorem pairDiophantine : PairDiophantine := by
  intro alpha f g hf hg
  have hF : DiophFn (fun v : Option alpha → Nat => f (v ∘ some)) :=
    Dioph.reindex_diophFn some hf
  have hG : DiophFn (fun v : Option alpha → Nat => g (v ∘ some)) :=
    Dioph.reindex_diophFn some hg
  have hO : DiophFn (fun v : Option alpha → Nat => v none) := Dioph.proj_dioph none
  have h1 := (Dioph.lt_dioph hF hG).inter
    (Dioph.eq_dioph (Dioph.add_dioph (Dioph.mul_dioph hG hG) hF) hO)
  have h2 := (Dioph.le_dioph hG hF).inter
    (Dioph.eq_dioph (Dioph.add_dioph
      (Dioph.add_dioph (Dioph.mul_dioph hF hF) hF) hG) hO)
  apply (h1.union h2).ext
  intro v
  change ((f (v ∘ some) < g (v ∘ some) ∧
      g (v ∘ some) * g (v ∘ some) + f (v ∘ some) = v none) ∨
    (g (v ∘ some) ≤ f (v ∘ some) ∧
      f (v ∘ some) * f (v ∘ some) + f (v ∘ some) + g (v ∘ some) = v none)) ↔
    Nat.pair (f (v ∘ some)) (g (v ∘ some)) = v none
  by_cases h : f (v ∘ some) < g (v ∘ some)
  · simp [Nat.pair, h, Nat.not_le_of_gt h]
  · simp [Nat.pair, h, Nat.le_of_not_gt h]

theorem unpairDiophantine : UnpairDiophantine := by
  intro alpha f hf
  have hF : DiophFn (fun v : Option (Option alpha) → Nat =>
      f (v ∘ (fun i => some (some i)))) :=
    Dioph.reindex_diophFn (fun i => some (some i)) hf
  have hL := Dioph.eq_dioph
    (pairDiophantine _ _ _ (Dioph.proj_dioph (some none)) (Dioph.proj_dioph none)) hF
  have hR := Dioph.eq_dioph
    (pairDiophantine _ _ _ (Dioph.proj_dioph none) (Dioph.proj_dioph (some none))) hF
  constructor
  · apply (Dioph.ex1_dioph hL).ext
    intro v
    change (∃ b, Nat.pair (v none) b = f (v ∘ some)) ↔
      (Nat.unpair (f (v ∘ some))).1 = v none
    constructor
    · rintro ⟨b, hb⟩
      have h := congrArg (fun n => (Nat.unpair n).1) hb
      simpa using h.symm
    · intro h
      refine ⟨(Nat.unpair (f (v ∘ some))).2, ?_⟩
      rw [← h, Nat.pair_unpair]
  · apply (Dioph.ex1_dioph hR).ext
    intro v
    change (∃ a, Nat.pair a (v none) = f (v ∘ some)) ↔
      (Nat.unpair (f (v ∘ some))).2 = v none
    constructor
    · rintro ⟨a, ha⟩
      have h := congrArg (fun n => (Nat.unpair n).2) ha
      simpa using h.symm
    · intro h
      refine ⟨(Nat.unpair (f (v ∘ some))).1, ?_⟩
      rw [← h, Nat.pair_unpair]

theorem partialPairClosure : PartialPairClosure := by
  intro f g hf hg
  have hF : Dioph {v : Option (Option (Fin 2)) → Nat |
      v none ∈ f (v (some (some 0)))} := by
    simpa [graph, Function.comp_def] using
      Dioph.reindex_dioph _
        (fun i : Fin 2 => if i = 0 then some (some 0) else none) hf
  have hG : Dioph {v : Option (Option (Fin 2)) → Nat |
      v (some none) ∈ g (v (some (some 0)))} := by
    simpa [graph, Function.comp_def] using
      Dioph.reindex_dioph _
        (fun i : Fin 2 => if i = 0 then some (some 0) else some none) hg
  have hP := Dioph.eq_dioph
    (pairDiophantine _ _ _ (Dioph.proj_dioph none) (Dioph.proj_dioph (some none)))
    (Dioph.proj_dioph (some (some (1 : Fin 2))))
  apply (Dioph.ex1_dioph (Dioph.ex1_dioph ((hF.inter hG).inter hP))).ext
  intro v
  change (∃ b a, (a ∈ f (v 0) ∧ b ∈ g (v 0)) ∧ Nat.pair a b = v 1) ↔
    v 1 ∈ (f (v 0)).bind (fun a => (g (v 0)).map (Nat.pair a))
  rw [Part.mem_bind_iff]
  constructor
  · rintro ⟨b, a, ⟨ha, hb⟩, hp⟩
    exact ⟨a, ha, (Part.mem_map_iff _).mpr ⟨b, hb, hp⟩⟩
  · rintro ⟨a, ha, hab⟩
    obtain ⟨b, hb, hp⟩ := (Part.mem_map_iff _).mp hab
    exact ⟨b, a, ⟨ha, hb⟩, hp⟩

theorem partialCompositionClosure : PartialCompositionClosure := by
  intro f g hf hg
  have hG : Dioph {v : Option (Fin 2) → Nat | v none ∈ g (v (some 0))} := by
    simpa [graph, Function.comp_def] using
      Dioph.reindex_dioph _ (fun i : Fin 2 => if i = 0 then some 0 else none) hg
  have hF : Dioph {v : Option (Fin 2) → Nat | v (some 1) ∈ f (v none)} := by
    simpa [graph, Function.comp_def] using
      Dioph.reindex_dioph _ (fun i : Fin 2 => if i = 0 then none else some 1) hf
  apply (Dioph.ex1_dioph (hG.inter hF)).ext
  intro v
  change (∃ m, m ∈ g (v 0) ∧ v 1 ∈ f m) ↔ v 1 ∈ (g (v 0)).bind f
  exact Part.mem_bind_iff.symm

theorem recursionFreeGraphDiophantine : RecursionFreeGraphDiophantine := by
  intro c hc
  induction hc with
  | zero =>
      apply (Dioph.eq_dioph (Dioph.const_dioph 0) (Dioph.proj_dioph (1 : Fin 2))).ext
      intro v
      simp [graph, Nat.Partrec.Code.eval, pure, PFun.pure, eq_comm]
  | succ =>
      apply (Dioph.eq_dioph
        (Dioph.add_dioph (Dioph.proj_dioph (0 : Fin 2)) (Dioph.const_dioph 1))
        (Dioph.proj_dioph (1 : Fin 2))).ext
      intro v
      simp [graph, Nat.Partrec.Code.eval, Nat.succ_eq_add_one, eq_comm]
  | left =>
      apply (Dioph.eq_dioph
        (unpairDiophantine _ _ (Dioph.proj_dioph (0 : Fin 2))).1
        (Dioph.proj_dioph (1 : Fin 2))).ext
      intro v
      simp [graph, Nat.Partrec.Code.eval, eq_comm]
  | right =>
      apply (Dioph.eq_dioph
        (unpairDiophantine _ _ (Dioph.proj_dioph (0 : Fin 2))).2
        (Dioph.proj_dioph (1 : Fin 2))).ext
      intro v
      simp [graph, Nat.Partrec.Code.eval, eq_comm]
  | pair hf hg ihf ihg =>
      apply (partialPairClosure _ _ ihf ihg).ext
      intro v
      simp [graph, partialPair, Nat.Partrec.Code.eval, Seq.seq,
        Part.mem_bind_iff, Part.mem_map_iff]
  | comp hf hg ihf ihg =>
      exact partialCompositionClosure _ _ ihf ihg

theorem recursionFreePolynomialRepresentation : RecursionFreePolynomialRepresentation := by
  intro c hc
  exact (DiophantinePolynomialBridgeProof.diophantineCodeRepresentation 2 _).mp
    (recursionFreeGraphDiophantine c hc)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Proof
