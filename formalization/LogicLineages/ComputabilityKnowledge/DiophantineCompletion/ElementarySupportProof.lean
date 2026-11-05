module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementarySupportProof
open Elementary ElementaryTargets

theorem naturalPairRepresentation : NaturalPairRepresentation := by
  intro α f hf
  induction hf with
  | proj i =>
      exact ⟨.variable i,.constant 0,fun ν => by simp [Expr.eval]⟩
  | const z =>
      refine ⟨.constant z.toNat,.constant (-z).toNat,?_⟩
      intro ν
      change z=(z.toNat : Int)-((-z).toNat : Int)
      omega
  | sub hf hg ihf ihg =>
      obtain ⟨p,q,hf⟩ := ihf
      obtain ⟨r,s,hg⟩ := ihg
      refine ⟨.add p s,.add q r,?_⟩
      intro ν
      simp only [Expr.eval,Nat.cast_add]
      rw [hf ν,hg ν]
      ring
  | mul hf hg ihf ihg =>
      obtain ⟨p,q,hf⟩ := ihf
      obtain ⟨r,s,hg⟩ := ihg
      refine ⟨.add (.mul p r) (.mul q s),.add (.mul p s) (.mul q r),?_⟩
      intro ν
      simp only [Expr.eval,Nat.cast_add,Nat.cast_mul]
      rw [hf ν,hg ν]
      ring

theorem renameHolds {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (c : Constraint α β) (ν : γ → Nat) (w : δ → Nat) :
    (c.rename f g).Holds ν w ↔ c.Holds (ν ∘ f) (w ∘ g) := by
  obtain ⟨o,r⟩ := c
  cases r <;> rfl

theorem moveHolds {α β γ : Type} (c : Constraint (α ⊕ β) γ)
    (ν : α → Nat) (w : β ⊕ γ → Nat) :
    c.moveParameters.Holds ν w ↔
      c.Holds (Sum.elim ν (fun b => w (.inl b))) (fun b => w (.inr b)) := by
  obtain ⟨o,r⟩ := c
  cases r with
  | constant c => rfl
  | «variable» i => rfl
  | «parameter» a => cases a <;> rfl
  | add i j => rfl
  | mul i j => rfl

theorem representsExt {α : Type} {S T : Set (α → Nat)}
    (h : Represents S) (he : ∀ ν, ν ∈ S ↔ ν ∈ T) : Represents T := by
  obtain ⟨k,m,C,hC⟩ := h
  exact ⟨k,m,C,fun ν => (he ν).symm.trans (hC ν)⟩

/-- Convert arbitrary finite witness/equation types to explicit finite
natural blocks; no positivity restriction is introduced. -/
theorem finiteSystem {α β ι : Type} [Fintype β] [Fintype ι]
    (C : ι → Constraint α β) :
    Represents {ν : α → Nat | ∃ w : β → Nat, ∀ j : ι, (C j).Holds ν w} := by
  classical
  let e := Fintype.equivFin β
  let d := Fintype.equivFin ι
  refine ⟨Fintype.card β,Fintype.card ι,fun j => (C (d.symm j)).rename id e,?_⟩
  intro ν
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨fun b => w (e.symm b),?_⟩
    intro j
    rw [renameHolds]
    simpa [Function.comp_def] using hw (d.symm j)
  · rintro ⟨w,hw⟩
    refine ⟨fun b => w (e b),?_⟩
    intro j
    have h := hw (d j)
    rw [renameHolds] at h
    simpa [Function.comp_def] using h

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementarySupportProof
