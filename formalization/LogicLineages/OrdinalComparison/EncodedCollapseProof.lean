module
public import LogicLineages.OrdinalComparison.EncodedCollapseTargets
public import LogicLineages.OrdinalComparison.EncodedDescentProof
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem encodedTrajectoryCorrect : Targets.EncodedTrajectoryCorrect := by
  intro a k
  induction k with
  | zero =>
      intro _
      change ONote.NF (rawNoteDecode (rawNoteEncode a.1)) ∧
        (rawNoteDecode (rawNoteEncode a.1)).repr = a.1.repr
      rw [rawNoteDecodeEncode a.1]
      exact ⟨a.2, rfl⟩
  | succ k ih =>
      intro hk
      have hlt : k < actualReplacementCount a.1.repr := by omega
      have hp := ih (by omega)
      let r : NONote := ⟨rawNoteDecode (encodedStateAfter (rawNoteEncode a.1) k), hp.1⟩
      have hr : Ordinal.omega0 ≤ r.1.repr := by
        rw [hp.2]
        exact (actualTerminalFirstFinite a.1.repr (normalRepresentationSound a)).2 k hlt
      have hs := encodedDescentStepCorrect r hr
      rw [rawNoteEncodeDecode (encodedStateAfter (rawNoteEncode a.1) k)] at hs
      have hnext : encodedStateAfter (rawNoteEncode a.1) (k + 1) =
          encodedDescentStep (encodedStateAfter (rawNoteEncode a.1) k) := by
        simp only [encodedStateAfter, Function.iterate_succ_apply']
      rw [hnext]
      refine ⟨hs.1, ?_⟩
      rw [hs.2, hp.2, Function.iterate_succ_apply']

theorem encodedFirstFiniteCorrect : Targets.EncodedFirstFiniteCorrect := by
  intro a
  let c := rawNoteEncode a.1
  let t := actualReplacementCount a.1.repr
  have hs := actualTerminalFirstFinite a.1.repr (normalRepresentationSound a)
  have ht := encodedTrajectoryCorrect a t le_rfl
  let z : NONote := ⟨rawNoteDecode (encodedStateAfter c t), ht.1⟩
  have hz : z.1.repr = (actualTerminalValue a.1.repr : Ordinal) := ht.2.trans hs.1
  have hzcode : rawNoteEncode z.1 = encodedStateAfter c t := rawNoteEncodeDecode _
  have hf := (encodedFiniteCorrect z).1.mpr (by
    rw [hz]
    exact Ordinal.natCast_lt_omega0 _)
  rw [hzcode] at hf
  have hsearch : t ∈ encodedTerminalSearch c := by
    apply Nat.mem_rfind.mpr
    constructor
    · exact Part.mem_some_iff.mpr hf.symm
    · intro m hm
      have hmtraj := encodedTrajectoryCorrect a m hm.le
      let r : NONote := ⟨rawNoteDecode (encodedStateAfter c m), hmtraj.1⟩
      have hrcode : rawNoteEncode r.1 = encodedStateAfter c m := rawNoteEncodeDecode _
      have hnon := hs.2 m hm
      have hfalse : encodedFiniteTest (encodedStateAfter c m) = false := by
        cases h : encodedFiniteTest (encodedStateAfter c m) with
        | false => rfl
        | true =>
            have hfinite : r.1.repr < Ordinal.omega0 := (encodedFiniteCorrect r).1.mp (by
              rw [hrcode]
              exact h)
            have hfinite' : (actualDescentStep^[m]) a.1.repr < Ordinal.omega0 := by
              rw [← hmtraj.2]
              exact hfinite
            exact False.elim ((not_lt_of_ge hnon) hfinite')
      exact Part.mem_some_iff.mpr hfalse.symm
  refine ⟨hsearch, ?_⟩
  have hv := (encodedFiniteCorrect z).2 (by rw [hzcode]; exact hf)
  rw [hzcode, hz] at hv
  exact_mod_cast hv

private theorem actualCollapse_mem_program (a : NONote) :
    actualCollapse a.1.repr ∈ encodedCollapsePartial (rawNoteEncode a.1) := by
  have hn : rawNormalCode (rawNoteEncode a.1) = 1 := (rawNormalCorrect a.1).mpr a.2
  rw [encodedCollapsePartial, if_pos hn]
  have hs := encodedFirstFiniteCorrect a
  have hm := Part.mem_map (fun k => encodedFiniteValue (encodedStateAfter (rawNoteEncode a.1) k) + k) hs.1
  rw [hs.2, ← (actualTerminalValueIdentities a.1.repr (normalRepresentationSound a)).1] at hm
  exact hm

theorem encodedCollapsePartialRecursive : Targets.EncodedCollapsePartialRecursive := by
  have hi : Primrec₂ encodedStateAfter := encodedStateAfterPrimitiveRecursive
  have ht : Primrec encodedFiniteTest := encodedFiniteAlgorithmsPrimitiveRecursive.1
  have hv : Primrec encodedFiniteValue :=
    Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2
  have hp : Primrec (fun p : Nat × Nat => encodedFiniteTest (encodedStateAfter p.1 p.2)) :=
    ht.comp hi
  have hsearch : Partrec encodedTerminalSearch := Partrec.rfind hp.to_comp.partrec.to₂
  have hresult : Primrec (fun p : Nat × Nat => encodedFiniteValue (encodedStateAfter p.1 p.2) + p.2) :=
    Primrec.nat_add.comp (hv.comp hi) Primrec.snd
  have hbranch : Partrec (fun n =>
      (encodedTerminalSearch n).map (fun k => encodedFiniteValue (encodedStateAfter n k) + k)) :=
    hsearch.map hresult.to_comp.to₂
  have hn : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hguard : PrimrecPred (fun n : Nat => rawNormalCode n = 1) :=
    Primrec.eq.comp hn (Primrec.const 1)
  let flag : Nat → Nat := fun n => if rawNormalCode n = 1 then 1 else 0
  have hflag : Computable flag :=
    (Primrec.ite hguard (Primrec.const 1) (Primrec.const 0)).to_comp
  have hbranchPair : Partrec (fun p : Nat × Nat =>
      (encodedTerminalSearch p.1).map (fun k => encodedFiniteValue (encodedStateAfter p.1 k) + k)) :=
    hbranch.comp Computable.fst
  exact (Partrec.nat_casesOn_right hflag (Computable.const 0) hbranchPair.to₂).of_eq (fun n => by
    by_cases h : rawNormalCode n = 1 <;> simp [flag, h, encodedCollapsePartial])

theorem encodedCollapseTotal : Targets.EncodedCollapseTotal := by
  intro n
  by_cases hn : rawNormalCode n = 1
  · let a : NONote := ⟨rawNoteDecode n, (rawNormalDecodeCorrect n).mp hn⟩
    have hm := actualCollapse_mem_program a
    rw [rawNoteEncodeDecode n] at hm
    exact hm.1
  · simp [encodedCollapsePartial, hn]

theorem encodedCollapseComputable : Targets.EncodedCollapseComputable := by
  apply encodedCollapsePartialRecursive.of_eq_tot
  intro n
  classical
  unfold encodedCollapseValue
  rw [Part.getOrElse_of_dom _ (encodedCollapseTotal n) 0]
  exact Part.get_mem (encodedCollapseTotal n)

theorem encodedCollapseSourceCorrect : Targets.EncodedCollapseSourceCorrect := by
  intro a
  classical
  have hm := actualCollapse_mem_program a
  unfold encodedCollapseValue
  exact (Part.getOrElse_of_dom _ hm.1 0).trans (Part.get_eq_of_mem hm hm.1)

theorem fullEncodedClosedEvaluation : Targets.FullEncodedClosedEvaluation :=
  ⟨encodedFiniteCorrect, encodedDescentStepCorrect, encodedDescentStepFiniteFixed,
    encodedStateAfterPrimitiveRecursive, encodedTrajectoryCorrect, encodedFirstFiniteCorrect,
    encodedCollapsePartialRecursive, encodedCollapseTotal, encodedCollapseSourceCorrect,
    encodedCollapseComputable⟩

end LogicLineages.OrdinalComparison
