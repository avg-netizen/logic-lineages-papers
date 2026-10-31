module
public import LogicLineages.OrdinalComparison.SourceSortCompletionTargets
public import LogicLineages.OrdinalComparison.SourceSuccessorCodingProof
public import Mathlib.Data.List.Permutation
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSortCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem probe_assignment (Γ : List Ty) (x : Variable Γ .ground) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (successorProbe x) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground, x, 0⟩))) := by
  simp only [successorProbe, AdmissibleAssignment.assignment]
  apply congrArg Option.some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [AdmissibleAssignment.application, AdmissibleAssignment.box,
    AdmissibleAssignment.boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level]

private theorem observation_exact (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (x : Variable Γ .ground) (y : Nat) :
    Observation ρ (successorProbe x) y ↔ y = successorObservation (input ρ x) := by
  have hd := SourceSuccessorCodingProof.successorProbeDenotation Γ x
    (fun c => ((ρ c + 1 : Nat) : Ordinal)) (input ρ x)
    (fun _ => .collapse .one (.add .one (.var ⟨.ground, x, 0⟩))) rfl
    (SourceApplicativeProof.successorProbeAssignment Γ x)
  have hc := SourceSuccessorCodingProof.successorObservationCalibration (input ρ x)
  have hr : successorRaw (input ρ x) = successorObservation (input ρ x) + 1 := by omega
  rw [hr] at hd
  constructor
  · rintro ⟨v, hv, he⟩
    rw [probe_assignment] at hv
    cases Option.some.inj hv
    rw [hd] at he
    have hn : successorObservation (input ρ x) + 1 = y + 1 := by exact_mod_cast he
    omega
  · intro hy
    subst y
    exact ⟨_, probe_assignment Γ x, hd⟩

theorem fullSourceSort : Targets.FullSourceSort := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ ρ x y
    rw [observation_exact, (SourceSuccessorCodingProof.successorObservationCalibration (input ρ x)).2]
  · intro a b c d
    rw [SourceSuccessorCodingProof.successorPairCoding]
    change ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ↔
      (([a,b] : List Nat) : Multiset Nat) = (([c,d] : List Nat) : Multiset Nat)
    rw [Multiset.coe_eq_coe, List.perm_pair]
    simp
  · intro Γ ρ a b low high difference
    unfold SortFormula
    simp only [observation_exact]
    rw [← SourceSuccessorCodingProof.successorSortedWitness
      (input ρ a) (input ρ b) (input ρ low) (input ρ high) difference]
    constructor
    · rintro ⟨qa, qb, qlow, qhigh, rfl, rfl, rfl, rfl, hs, hd⟩
      exact ⟨hs, hd⟩
    · rintro ⟨hs, hd⟩
      exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, hs, hd⟩
end LogicLineages.OrdinalComparison.Source.SourceSortCompletion.Proof
