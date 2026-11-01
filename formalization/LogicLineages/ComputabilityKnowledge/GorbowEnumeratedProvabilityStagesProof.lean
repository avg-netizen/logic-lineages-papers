module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! A real c.e. axiom theory is the increasing union of its bounded-stage
axiom theories. Every finite typed Hilbert derivation is already captured at
one common finite stage; generalization adds no infinitary assumption. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StagesProof
open GorbowSyntax GorbowTheoryProof

theorem uniformAxiomChecker : Targets.UniformAxiomChecker := by
  have hf : Primrec (fun p : Parameters × List Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun p : Parameters × List Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : Parameters × List Nat => Encodable.encode p.2) :=
    Primrec.encode.comp Primrec.snd
  have he := Nat.Partrec.Code.primrec_evaln.comp ((hf.pair hc).pair hr)
  exact (Primrec.eq.comp he (Primrec.const (some 1))).decide

theorem boundedMonotonicity : Targets.BoundedMonotonicity := by
  intro c s t hst sigma hs
  change decide (Nat.Partrec.Code.evaln s c _ = some 1) = true at hs
  change decide (Nat.Partrec.Code.evaln t c _ = some 1) = true
  simp only [decide_eq_true_eq] at hs ⊢
  exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hs))

theorem exactAxiomUnion : Targets.ExactAxiomUnion := by
  intro c sigma
  change 1 ∈ c.eval _ ↔ ∃ fuel, decide (Nat.Partrec.Code.evaln fuel c _ = some 1) = true
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨fuel, hf⟩ := Nat.Partrec.Code.evaln_complete.mp h
    exact ⟨fuel, Option.mem_def.mp hf⟩
  · rintro ⟨fuel, hf⟩
    exact Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hf)

private theorem captures {c : Code} {n : Nat} {phi : Formula n}
    (p : Derivation (enumeratedTheory c) phi) :
    ∃ fuel, Nonempty (Derivation (boundedTheory (c,fuel)) phi) := by
  induction p with
  | logical w => exact ⟨0, ⟨.logical w⟩⟩
  | arithmetic w => exact ⟨0, ⟨.arithmetic w⟩⟩
  | «axiom» sigma h =>
    obtain ⟨fuel, hf⟩ := (exactAxiomUnion c sigma).mp h
    exact ⟨fuel, ⟨.axiom sigma hf⟩⟩
  | @mp n a b p q hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    obtain ⟨ps⟩ := GorbowTheoryProofProof.monotonicity
      (boundedTheory (c,s)) (boundedTheory (c,max s t))
      (boundedMonotonicity c s (max s t) (le_max_left s t)) n (.imp a b) hs
    obtain ⟨pt⟩ := GorbowTheoryProofProof.monotonicity
      (boundedTheory (c,t)) (boundedTheory (c,max s t))
      (boundedMonotonicity c t (max s t) (le_max_right s t)) n a ht
    exact ⟨max s t, ⟨.mp ps pt⟩⟩
  | generalize p hp =>
    obtain ⟨fuel, ⟨pf⟩⟩ := hp
    exact ⟨fuel, ⟨.generalize pf⟩⟩

theorem finiteProofStage : Targets.FiniteProofStage := by
  intro c n phi
  constructor
  · rintro ⟨p⟩
    exact captures p
  · rintro ⟨fuel, hp⟩
    exact GorbowTheoryProofProof.monotonicity (boundedTheory (c,fuel)) (enumeratedTheory c)
      (fun sigma hs => (exactAxiomUnion c sigma).mpr ⟨fuel, hs⟩) n phi hp

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StagesProof
