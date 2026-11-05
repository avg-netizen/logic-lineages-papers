module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryExpressionProof
public import LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridgeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryNormalizationProof
open Dioph Elementary ElementaryTargets ElementarySupportProof

private theorem constraintDiophantine {α β : Type} (c : Constraint α β) :
    Dioph {v : α ⊕ β → Nat | c.Holds (fun a => v (.inl a)) (fun b => v (.inr b))} := by
  obtain ⟨o,r⟩ := c
  have ho : DiophFn (fun v : α ⊕ β → Nat => v (Sum.inr o)) := Dioph.proj_dioph _
  cases r with
  | constant c =>
      exact Dioph.eq_dioph ho (Dioph.const_dioph c)
  | «variable» i =>
      exact Dioph.eq_dioph ho (Dioph.proj_dioph (Sum.inr i : α ⊕ β))
  | «parameter» a =>
      exact Dioph.eq_dioph ho (Dioph.proj_dioph (Sum.inl a : α ⊕ β))
  | add i j =>
      exact Dioph.eq_dioph ho (Dioph.add_dioph
        (Dioph.proj_dioph (Sum.inr i : α ⊕ β)) (Dioph.proj_dioph (Sum.inr j : α ⊕ β)))
  | mul i j =>
      exact Dioph.eq_dioph ho (Dioph.mul_dioph
        (Dioph.proj_dioph (Sum.inr i : α ⊕ β)) (Dioph.proj_dioph (Sum.inr j : α ⊕ β)))

private theorem constraintListDiophantine {α β : Type} (L : List (Constraint α β)) :
    Dioph {v : α ⊕ β → Nat | ∀ c ∈ L, c.Holds (fun a => v (.inl a)) (fun b => v (.inr b))} := by
  induction L with
  | nil =>
      exact (Dioph.eq_dioph (Dioph.const_dioph (0 : Nat)) (Dioph.const_dioph 0)).ext (fun v => by simp)
  | cons c L ih =>
      exact ((constraintDiophantine c).inter ih).ext (fun v => by simp)

theorem representedDiophantine {α : Type} {S : Set (α → Nat)} (h : Represents S) : Dioph S := by
  obtain ⟨k,m,C,hC⟩ := h
  have hf : Dioph {v : α ⊕ Fin k → Nat |
      ∀ j : Fin m, (C j).Holds (fun a => v (.inl a)) (fun b => v (.inr b))} := by
    apply (constraintListDiophantine (List.ofFn C)).ext
    intro v
    constructor
    · intro hl j
      exact hl (C j) (List.mem_ofFn.mpr ⟨j,rfl⟩)
    · intro hj c hc
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      exact hj j
  exact (Dioph.ex_dioph hf).ext (fun ν => (hC ν).symm)

theorem diophantineRepresented (n : Nat) (S : Set (Fin n → Nat)) (hS : Dioph S) : Represents S := by
  obtain ⟨m,P,hP⟩ := (DiophantinePolynomialBridgeProof.finiteWitnessExtraction n S).1 hS
  let f : (Fin n ⊕ Fin m → Nat) → Int :=
    fun v => MvPolynomial.eval (fun i => (v i : Int)) P
  have hf : IsPoly f :=
    (DiophantinePolynomialBridgeProof.polynomialCorrespondence (Fin n ⊕ Fin m) f).2 ⟨P,fun _ => rfl⟩
  obtain ⟨p,q,hpq⟩ := naturalPairRepresentation (Fin n ⊕ Fin m) f hf
  obtain ⟨k,l,C,hC⟩ := ElementaryExpressionProof.expressionSystemNormalization (Fin n ⊕ Fin m) p q
  have hMoved := finiteSystem (fun j : Fin l => (C j).moveParameters)
  apply representsExt hMoved
  intro ν
  constructor
  · rintro ⟨τ,hτ⟩
    let w : Fin m → Nat := fun b => τ (.inl b)
    let z : Fin k → Nat := fun b => τ (.inr b)
    have hc : ∀ j, (C j).Holds (Sum.elim ν w) z :=
      fun j => (moveHolds (C j) ν τ).1 (hτ j)
    have he : p.eval (Sum.elim ν w)=q.eval (Sum.elim ν w) :=
      (hC (Sum.elim ν w)).2 ⟨z,hc⟩
    have hz : f (Sum.elim ν w)=0 := by
      rw [hpq]
      exact sub_eq_zero.mpr (congrArg (fun a : Nat => (a : Int)) he)
    exact (hP ν).2 ⟨w,hz⟩
  · intro hν
    obtain ⟨w,hw⟩ := (hP ν).1 hν
    have hz : f (Sum.elim ν w)=0 := hw
    have he : p.eval (Sum.elim ν w)=q.eval (Sum.elim ν w) :=
      Int.ofNat_inj.mp (sub_eq_zero.mp ((hpq (Sum.elim ν w)).symm.trans hz))
    obtain ⟨z,hz⟩ := (hC (Sum.elim ν w)).1 he
    refine ⟨Sum.elim w z,?_⟩
    intro j
    exact (moveHolds (C j) ν (Sum.elim w z)).2 (hz j)

theorem elementarySystemNormalization : ElementarySystemNormalization := by
  intro n S
  exact ⟨diophantineRepresented n S,representedDiophantine⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryNormalizationProof
