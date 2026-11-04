module
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

/-- The witness-code test is jointly computable for each fixed gamma. -/
theorem testComputable (b : Nat) : Computable (fun p : Nat × Nat => test b p.1 p.2) := by
  have hd : Primrec (fun p : Nat × Nat => Encodable.decode (α := List Nat) p.2) :=
    Primrec.decode.comp Primrec.snd
  have hb : Computable (fun p : (Nat × Nat) × List Nat =>
      SourceGammaCounterexample.counterexample b p.1.1 p.2) :=
    (SourceGammaCounterexample.Proof.fixedComputable b).comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have h : Computable (fun p : Nat × Nat =>
      (Encodable.decode (α := List Nat) p.2).casesOn (motive := fun _ => Bool)
        false (fun xs => SourceGammaCounterexample.counterexample b p.1 xs)) :=
    Computable.option_casesOn hd.to_comp (Computable.const false) hb.to₂
  apply h.of_eq
  intro p
  unfold test
  cases Encodable.decode (α := List Nat) p.2 <;> rfl

/-- The literal least-witness search is partial recursive. -/
theorem searchPartrec (b : Nat) : Partrec (search b) :=
  Partrec.rfind (testComputable b).partrec.to₂
end LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Proof
