module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadFreshWireAllocation (install)
open ArbitraryHeadWireList (NormalGate normalizeGate)
open OriginalPrintedCircuitSequential (Gate Graphs)

private theorem allCons {A : Type} (P : A → Prop) (g : A) (gs : List A) :
    (∀ p ∈ g :: gs, P p) ↔ P g ∧ (∀ p ∈ gs, P p) := by
  constructor
  · intro h
    exact ⟨h g List.mem_cons_self,fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨head,tail⟩ p hp
    rcases List.mem_cons.mp hp with eq | rest
    · subst p
      exact head
    · exact tail p rest

theorem normalizedSplit (f : Nat → Nat) (θ : Valuation) (gates : List Gate) (n : Nat) :
    Holds f θ (normalizeFrom n gates) ↔
      OriginalMixedGateNormalization.Holds f θ
        (OriginalMixedGateNormalization.normalizeFrom n (baseGates gates)) ∧ FieldsAt f θ gates := by
  induction gates generalizing n with
  | nil =>
      simp [Holds,normalizeFrom,FieldsAt,baseGates,OriginalMixedGateNormalization.Holds,
        OriginalMixedGateNormalization.normalizeFrom]
  | cons g gs ih =>
      cases g with
      | base g =>
          cases g with
          | affine e o =>
              unfold Holds OriginalMixedGateNormalization.Holds at *
              change (∀ p ∈ NormalizedGate.base (.affine e o) :: normalizeFrom n gs, p.graph f θ) ↔
                (∀ p ∈ NormalGate.affine e o ::
                  OriginalMixedGateNormalization.normalizeFrom n (baseGates gs), p.Holds f θ) ∧
                    FieldsAt f θ gs
              rw [allCons,allCons,ih]
              exact and_assoc.symm
          | collapse w =>
              unfold Holds OriginalMixedGateNormalization.Holds at *
              change (∀ p ∈ NormalizedGate.base (normalizeGate (install w n)) ::
                  normalizeFrom (n+1) gs, p.graph f θ) ↔
                (∀ p ∈ normalizeGate (install w n) ::
                  OriginalMixedGateNormalization.normalizeFrom (n+1) (baseGates gs), p.Holds f θ) ∧
                    FieldsAt f θ gs
              rw [allCons,allCons,ih]
              exact and_assoc.symm
      | field g =>
          unfold Holds OriginalMixedGateNormalization.Holds at *
          change (∀ p ∈ NormalizedGate.field g :: normalizeFrom n gs, p.graph f θ) ↔
            (∀ p ∈ OriginalMixedGateNormalization.normalizeFrom n (baseGates gs), p.Holds f θ) ∧
              (g.graph f θ ∧ FieldsAt f θ gs)
          rw [allCons,ih]
          constructor
          · rintro ⟨hd,hb,hf⟩
            exact ⟨hb,hd,hf⟩
          · rintro ⟨hb,hd,hf⟩
            exact ⟨hd,hb,hf⟩

theorem originalSplit (f : Nat → Nat) (θ : Valuation) (gates : List Gate) :
    Graphs f θ gates ↔ OriginalMixedGateSequential.Graphs f θ (baseGates gates) ∧ FieldsAt f θ gates := by
  induction gates with
  | nil => simp [Graphs,OriginalMixedGateSequential.Graphs,baseGates,FieldsAt]
  | cons g gs ih =>
      unfold Graphs OriginalMixedGateSequential.Graphs at *
      rw [allCons,ih]
      cases g with
      | base g =>
          change g.graph f θ ∧ ((∀ p ∈ baseGates gs, p.graph f θ) ∧ FieldsAt f θ gs) ↔
            (∀ p ∈ g :: baseGates gs, p.graph f θ) ∧ FieldsAt f θ gs
          rw [allCons]
          exact and_assoc.symm
      | field g =>
          change g.graph f θ ∧ ((∀ p ∈ baseGates gs, p.graph f θ) ∧ FieldsAt f θ gs) ↔
            (∀ p ∈ baseGates gs, p.graph f θ) ∧ (g.graph f θ ∧ FieldsAt f θ gs)
          constructor
          · rintro ⟨hd,hb,hf⟩
            exact ⟨hb,hd,hf⟩
          · rintro ⟨hb,hd,hf⟩
            exact ⟨hd,hb,hf⟩

theorem fieldsStable (f : Nat → Nat) (ν θ : Valuation) (gates : List Gate)
    (same : ∀ g ∈ gates, θ g.output = ν g.output ∧ ∀ n ∈ g.references, θ n = ν n) :
    FieldsAt f θ gates ↔ FieldsAt f ν gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      have tail := ih (fun q hq => same q (List.mem_cons_of_mem _ hq))
      cases g with
      | base g => exact tail
      | field g =>
          have unchanged := same (Gate.field g) List.mem_cons_self
          have stable := (OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f g ν θ).2 unchanged.2
          exact and_congr (stable.2 unchanged.1) tail

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
