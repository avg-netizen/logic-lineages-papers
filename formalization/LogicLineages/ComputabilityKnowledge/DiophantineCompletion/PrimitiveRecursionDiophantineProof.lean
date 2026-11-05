module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionSemanticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDigitProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Proof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDiophantineProof
open Dioph PrimitiveRecursion PrimitiveRecursionTargets RowPackingClosureProof PrimitiveRecursionDigitProof

private theorem graphOnFunctions {α : Type} (c : Nat.Partrec.Code)
    (hc : Dioph (graph (Nat.Partrec.Code.eval c)))
    (f g : (α → Nat) → Nat) (hf : DiophFn f) (hg : DiophFn g) :
    Dioph {v | g v ∈ Nat.Partrec.Code.eval c (f v)} := by
  exact finCompose hc ![f,g] (by
    intro i
    fin_cases i
    · exact hf
    · exact hg)

/-- Only a coordinate transport of the proved closure, not a new premise. -/
private theorem finiteBoundedUniversal {α : Type} [Fintype α]
    (bound : (α → Nat) → Nat) (R : Nat → (α → Nat) → Prop)
    (hb : DiophFn bound) (hR : Dioph {v : Option α → Nat | R (v none) (v ∘ some)}) :
    Dioph {v : α → Nat | ∀ i, i < bound v → R i v} := by
  classical
  let e := Fintype.equivFin α
  have hB := Dioph.reindex_diophFn e hb
  have hRel := Dioph.reindex_dioph (Option (Fin (Fintype.card α))) (Option.map e) hR
  have hAll := BoundedUniversalProof.variableBoundedUniversalClosure (Fintype.card α)
    (fun v => bound (v ∘ e)) (fun i v => R i (v ∘ e)) hB hRel
  apply (Dioph.reindex_dioph α e.symm hAll).ext
  intro v
  change (∀ i, i < bound ((v ∘ e.symm) ∘ e) → R i ((v ∘ e.symm) ∘ e)) ↔ _
  have he : (v ∘ e.symm) ∘ e = v := by
    funext a
    simp [Function.comp_def]
  rw [he]
  rfl

theorem codedPrecTraceDiophantine : CodedPrecTraceDiophantine := by
  intro base step hb hs
  let α := Fin 3 ⊕ Fin 2
  let A : (α → Nat) → Nat := fun v => v (.inl 0)
  let N : (α → Nat) → Nat := fun v => v (.inl 1)
  let Y : (α → Nat) → Nat := fun v => v (.inl 2)
  let Q : (α → Nat) → Nat := fun v => v (.inr 0)
  let C : (α → Nat) → Nat := fun v => v (.inr 1)
  have hA : DiophFn A := Dioph.proj_dioph _
  have hN : DiophFn N := Dioph.proj_dioph _
  have hY : DiophFn Y := Dioph.proj_dioph _
  have hQ : DiophFn Q := Dioph.proj_dioph _
  have hC : DiophFn C := Dioph.proj_dioph _
  have hValid := finCompose CipherRelationDiophantineProof.codeDiophantine
    ![(fun v => N v + 1),Q,C] (by
      intro i
      fin_cases i
      · exact Dioph.add_dioph hN (Dioph.const_dioph 1)
      · exact hQ
      · exact hC)
  have hBase := graphOnFunctions base hb A (fun v => digit (Q v) (C v) 0) hA
    (digitDiophantine _ _ _ _ hQ hC (Dioph.const_dioph 0))
  let R : Nat → (α → Nat) → Prop := fun i v =>
    digit (Q v) (C v) (i + 1) ∈ Nat.Partrec.Code.eval step
      (Nat.pair (A v) (Nat.pair i (digit (Q v) (C v) i)))
  have hRel : Dioph {w : Option α → Nat | R (w none) (w ∘ some)} := by
    have hQ' := Dioph.reindex_diophFn some hQ
    have hC' := Dioph.reindex_diophFn some hC
    have hA' := Dioph.reindex_diophFn some hA
    have hI : DiophFn (fun w : Option α → Nat => w none) := Dioph.proj_dioph none
    have hDigit := digitDiophantine _ _ _ _ hQ' hC' hI
    have hNext := digitDiophantine _ _ _ _ hQ' hC'
      (Dioph.add_dioph hI (Dioph.const_dioph 1))
    exact graphOnFunctions step hs _ _
      (Proof.pairDiophantine _ _ _ hA' (Proof.pairDiophantine _ _ _ hI hDigit)) hNext
  have hSteps := finiteBoundedUniversal N R hN hRel
  have hEnd := Dioph.eq_dioph (digitDiophantine _ _ _ _ hQ hC hN) hY
  have hCore := hValid.inter ((hBase.inter hSteps).inter hEnd)
  apply (Dioph.ex_dioph hCore).ext
  intro v
  change (∃ w : Fin 2 → Nat, CipherRelation.Code (v 1 + 1) (w 0) (w 1) ∧
    partialTrace base step (v 0) (v 1) (digit (w 0) (w 1)) ∧ digit (w 0) (w 1) (v 1) = v 2) ↔
    ∃ q code : Nat, CipherRelation.Code (v 1 + 1) q code ∧
      partialTrace base step (v 0) (v 1) (digit q code) ∧ digit q code (v 1) = v 2
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w 0,w 1,hw⟩
  · rintro ⟨q,code,h⟩
    exact ⟨![q,code],h⟩

theorem ordinaryPrecGraphClosure : OrdinaryPrecGraphClosure := by
  intro base step hb hs
  have hInput := Proof.unpairDiophantine _ (fun v : Fin 2 → Nat => v 0) (Dioph.proj_dioph 0)
  have h := finCompose (codedPrecTraceDiophantine base step hb hs)
    ![(fun v : Fin 2 → Nat => (Nat.unpair (v 0)).1),
      (fun v => (Nat.unpair (v 0)).2),(fun v => v 1)] (by
        intro i
        fin_cases i
        · exact hInput.1
        · exact hInput.2
        · exact Dioph.proj_dioph 1)
  apply h.ext
  intro v
  change codedTrace base step (Nat.unpair (v 0)).1 (Nat.unpair (v 0)).2 (v 1) ↔
    v 1 ∈ Nat.Partrec.Code.eval (.prec base step) (v 0)
  simpa only [Nat.pair_unpair] using
    (PrimitiveRecursionSemanticProof.codedPrecTraceSpecification base step
      (Nat.unpair (v 0)).1 (Nat.unpair (v 0)).2 (v 1)).symm

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDiophantineProof
