module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityTargets
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

/-- Specialization is a literal primitive-recursive composition of program codes. -/
theorem exactSpecialization : Targets.ExactSpecialization := by
  constructor
  · exact Nat.Partrec.Code.primrec₂_comp.comp Primrec.fst
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd)
  · intro c n x
    change ((Nat.Partrec.Code.const n).eval x).bind c.eval = c.eval n
    rw [Nat.Partrec.Code.eval_const,Part.bind_some]

/-- One validated blank-machine translator works for every specialized program. -/
theorem uniformTranslator : Targets.UniformTranslator := by
  obtain ⟨U,hU,he⟩ := SourceBlankHaltingReduction.Proof.effectiveBlankReduction
  refine ⟨U,hU.comp (Primrec.encode.comp exactSpecialization.1),?_⟩
  intro c n
  change SourceBlankMachineSimulation.Halts
    (SourceBlankHaltingReduction.translate U (Encodable.encode (specialize c n))) ↔ _
  rw [he,exactSpecialization.2 c n 0]

private def recognizer (P : Nat → Prop) (n : Nat) : Part Nat :=
  (Part.assert (P n) (fun _ => Part.some ())).map (fun _ => 0)

private theorem recognizer_partrec (P : Nat → Prop) (hP : REPred P) : Partrec (recognizer P) := by
  have hp : Partrec (fun n : Nat => Part.assert (P n) (fun _ => Part.some ())) := hP
  have hz : Computable₂ (fun (_ : Nat) (_ : Unit) => (0 : Nat)) :=
    (Computable.const (0 : Nat) : Computable (fun _ : Nat × Unit => (0 : Nat))).to₂
  exact Partrec.map hp hz

private theorem recognizer_domain (P : Nat → Prop) (n : Nat) :
    (recognizer P n).Dom ↔ P n := by
  change (∃ _ : P n, True) ↔ P n
  simp

attribute [local irreducible] recognizer

private theorem fixed_code_domain (P : Nat → Prop) (hP : REPred P) :
    ∃ c : Nat.Partrec.Code, ∀ n : Nat, (c.eval n).Dom ↔ P n := by
  have hf : Nat.Partrec (recognizer P) := Partrec.nat_iff.mp (recognizer_partrec P hP)
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c,?_⟩
  intro n
  rw [hc]
  exact recognizer_domain P n

attribute [local irreducible] output specialize SourceBlankHaltingReduction.translate
attribute [local irreducible] SourceBlankMachineSimulation.Halts Primrec

private theorem fixed_output_primitive (U : Turing.ToPartrec.Code)
    (hU : Primrec (fun p : Nat.Partrec.Code × Nat => output U p.1 p.2))
    (c : Nat.Partrec.Code) : Primrec (fun n : Nat => output U c n) :=
  hU.comp ((Primrec.const c).pair Primrec.id)

/-- Every RE predicate has a primitive-recursive reduction to actual blank halting. -/
theorem reUniversality : Targets.REUniversality := by
  intro P hP
  obtain ⟨c,hdom⟩ := fixed_code_domain P hP
  obtain ⟨U,hU,he⟩ := uniformTranslator
  have hr : Primrec (fun n : Nat => output U c n) :=
    fixed_output_primitive U hU c
  have hexact : ∀ n : Nat, P n ↔ SourceBlankMachineSimulation.Halts (output U c n) :=
    fun n => (hdom n).symm.trans (he c n).symm
  exact ⟨⟨fun n => output U c n,hr,hexact⟩,
    ⟨fun n => output U c n,hr.to_comp,hexact⟩⟩
end LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality.Proof
