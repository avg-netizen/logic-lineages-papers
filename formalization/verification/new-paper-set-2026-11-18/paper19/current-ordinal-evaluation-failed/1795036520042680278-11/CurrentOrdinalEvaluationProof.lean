module
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeProof
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldProof
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelProof
public import LogicLineages.OrdinalComparison.EncodedNaturalProductProof
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoProof
public import LogicLineages.PermittedControl.EncodedEvaluatorProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluation

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ForwardTranslation

theorem growth_mono (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) :
    StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact ((f n).lt_two_pow_self.trans (2 ^ f n).lt_two_pow_self).trans_le (hf.2 n)

private theorem add_note (a b : NONote) :
    ∃ c : NONote, encodedNaturalSum (rawNoteEncode a.1) (rawNoteEncode b.1) =
      rawNoteEncode c.1 ∧ c.1.repr = ordinalNaturalSum a.1.repr b.1.repr := by
  obtain ⟨h, e, _⟩ := encodedNaturalSumSourceCorrect a b
  exact ⟨⟨_, h⟩, (rawNoteEncodeDecode _).symm, e⟩

private theorem mul_note (a b : NONote) :
    ∃ c : NONote, encodedNaturalProduct (rawNoteEncode a.1) (rawNoteEncode b.1) =
      rawNoteEncode c.1 ∧ c.1.repr = ordinalNaturalProduct a.1.repr b.1.repr := by
  obtain ⟨h, e, _⟩ := encodedNaturalProductSourceCorrect a b
  exact ⟨⟨_, h⟩, (rawNoteEncodeDecode _).symm, e⟩

private def omegaNote : NONote := ClosedPositive.omega.evaluate

private theorem omega_repr : omegaNote.1.repr = Ordinal.omega0 := by
  simp [omegaNote, ClosedPositive.evaluate, ONote.repr]

theorem calibration : CurrentOrdinalEvaluationTargets.Calibration := by
  intro f hf ι index t env ρ hρ
  unfold evaluate OrdinalSyntaxComputableFold.indexedFold
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  let ev := OrdinalSyntax.termFold index
    (fun k => leaf (env, k)) (fun k a b => branch f (env, k, a, b))
  change ∃ a : NONote, ev t = rawNoteEncode a.1 ∧
    a.1.repr = ParametricSourceSuccessor.denoteWith f (fun x => (ρ x : Ordinal)) t
  have native (n : Nat) : ∃ a : NONote,
      encodedNatNote n = rawNoteEncode a.1 ∧ a.1.repr = (n : Ordinal) :=
    ⟨⟨_, ONote.nf_ofNat n⟩, encodedNatNoteCorrect n, ONote.repr_ofNat n⟩
  induction t with
  | zero => simpa [ev, OrdinalSyntax.termFold, leaf, ParametricSourceSuccessor.denoteWith]
      using native 0
  | one => simpa [ev, OrdinalSyntax.termFold, leaf, ParametricSourceSuccessor.denoteWith]
      using native 1
  | omega => exact ⟨omegaNote, rfl, omega_repr⟩
  | var x =>
      have h1 : 8 * index x + 3 ≠ 1 := by omega
      have h2 : 8 * index x + 3 ≠ 2 := by omega
      have hm : (8 * index x + 3) % 8 = 3 := by omega
      have hd : (8 * index x + 3) / 8 = index x := by omega
      simpa [ev, OrdinalSyntax.termFold, leaf, h1, h2, hm, hd,
        ParametricSourceSuccessor.denoteWith, ← List.getD_eq_getElem?_getD, hρ x] using native (ρ x)
  | add a b iha ihb =>
      obtain ⟨na, ea, ra⟩ := iha
      obtain ⟨nb, eb, rb⟩ := ihb
      simpa [show ev (.add a b) = encodedNaturalSum (ev a) (ev b) from rfl,
        ea, eb, ParametricSourceSuccessor.denoteWith, ra, rb] using add_note na nb
  | emul a b iha ihb =>
      obtain ⟨na, ea, ra⟩ := iha
      obtain ⟨nb, eb, rb⟩ := ihb
      let pow := NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ na
      have hp : pow.1.repr = (2 : Ordinal) ^ na.1.repr := by
        show (ONote.opow (ONote.ofNat 2) na.1).repr = _
        rw [ONote.repr_opow, ONote.repr_ofNat]
        rfl
      simpa [show ev (.emul a b) = encodedNaturalProduct (encodedBaseTwoPower (ev a)) (ev b)
          from rfl, ea, eb, encodedBaseTwoPowerCorrect na, ParametricSourceSuccessor.denoteWith,
        hp, ra, rb] using mul_note pow nb
  | collapse a b iha ihb =>
      obtain ⟨na, ea, ra⟩ := iha
      obtain ⟨nm, em, rm⟩ := mul_note omegaNote na
      obtain ⟨nb, eb, rb⟩ := ihb
      obtain ⟨nc, ec, rc⟩ := add_note nm nb
      change ∃ c : NONote, encodedNatNote (PermittedControl.evaluatorWith f
          (encodedNaturalSum (encodedNaturalProduct omegaCode (ev a)) (ev b))) =
        rawNoteEncode c.1 ∧ c.1.repr =
          (ParametricActualCollapse.collapseWith f (ordinalNaturalSum
            (ordinalNaturalProduct Ordinal.omega0
              (ParametricSourceSuccessor.denoteWith f (fun x => (ρ x : Ordinal)) a))
            (ParametricSourceSuccessor.denoteWith f (fun x => (ρ x : Ordinal)) b)) : Ordinal)
      rw [ea, eb, show omegaCode = rawNoteEncode omegaNote.1 from rfl, em, ec,
        PermittedControl.evaluator_source f (growth_mono f hf) hf.1 nc, rc, rm, omega_repr, ra, rb]
      exact native _

theorem effective : CurrentOrdinalEvaluationTargets.Effective := by
  intro f hc hf
  apply OrdinalSyntaxComputableFold.Proof.indexedComputable
  · have htag : Primrec (fun p : List Nat × Nat => p.2 % 8) :=
      Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
    have hind : Primrec (fun p : List Nat × Nat => p.2 / 8) :=
      Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
    have hleaf : Primrec leaf := Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (Primrec.const _) (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2))
        (Primrec.const _) (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
          (encodedKernelBuildersPrimitiveRecursive.1.comp
            ((Primrec.list_getD 0).comp Primrec.fst hind)) (Primrec.const 0)))
    exact hleaf.to_comp
  · let P := List Nat × Nat × Nat × Nat
    have htag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
    have ha : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hb : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hsum := encodedNaturalSumPrimitiveRecursive
    have hmul := encodedNaturalProductPrimitiveRecursive
    have hpow := encodedBaseTwoPowerPrimitiveRecursive
    have hadd := hsum.comp ha hb
    have hemul := hmul.comp (hpow.comp ha) hb
    have harg := hsum.comp (hmul.comp (Primrec.const omegaCode) ha) hb
    have he := PermittedControl.evaluator_computable f hc (growth_mono f hf) hf.1
    have hcollapse := encodedKernelBuildersPrimitiveRecursive.1.to_comp.comp (he.comp harg.to_comp)
    exact Computable.ite (Primrec.eq.comp htag (Primrec.const 4)).to_comp hadd.to_comp
      (Computable.ite (Primrec.eq.comp htag (Primrec.const 5)).to_comp hemul.to_comp
        (Computable.ite (Primrec.eq.comp htag (Primrec.const 6)).to_comp hcollapse
          (Computable.const 0)))

end LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluation
