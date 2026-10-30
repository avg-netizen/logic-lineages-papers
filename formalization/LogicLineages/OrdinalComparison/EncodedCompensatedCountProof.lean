module
public import LogicLineages.OrdinalComparison.EncodedCompensatedCountTargets
public import LogicLineages.OrdinalComparison.EncodedCompensatedStepProof
public import LogicLineages.OrdinalComparison.ControlledCountProof
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem encodedCompensatedStatePrimitiveRecursive : Targets.EncodedCompensatedStatePrimitiveRecursive := by
  have hs : Primrec₂ encodedCompensatedStep := encodedCompensatedStepPrimitiveRecursive
  have hstep : Primrec₂ (fun (p : (Nat × Nat) × Nat) (x : Nat) => encodedCompensatedStep p.1.1 x) :=
    hs.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst) hstep

theorem encodedCompensatedTrajectoryCorrect : Targets.EncodedCompensatedTrajectoryCorrect := by
  intro c a k
  induction k with
  | zero =>
    intro _
    change ONote.NF (rawNoteDecode (rawNoteEncode a.1)) ∧ (rawNoteDecode (rawNoteEncode a.1)).repr=a.1.repr
    rw [rawNoteDecodeEncode a.1]
    exact ⟨a.2,rfl⟩
  | succ k ih =>
    intro hk
    have hlt : k < actualControlledCount (compensatedPrefixControl c) a.1.repr := by omega
    have hp := ih hlt.le
    let r : NONote := ⟨rawNoteDecode (encodedCompensatedState c (rawNoteEncode a.1) k),hp.1⟩
    have hr : Ordinal.omega0 ≤ r.1.repr := by
      rw [hp.2]
      exact ((actualControlledTraceFirstFinite (compensatedPrefixControl c) a.1.repr
        (normalRepresentationSound a)).2 k hlt.le).2.2 hlt
    have hs := encodedCompensatedStepCorrect c r hr
    rw [rawNoteEncodeDecode (encodedCompensatedState c (rawNoteEncode a.1) k)] at hs
    have hnext : encodedCompensatedState c (rawNoteEncode a.1) (k+1)=
        encodedCompensatedStep c (encodedCompensatedState c (rawNoteEncode a.1) k) := by
      simp only [encodedCompensatedState,Function.iterate_succ_apply']
    rw [hnext]
    refine ⟨hs.1,?_⟩
    rw [hs.2,hp.2,actualControlledStateAfter_succ]

theorem encodedCompensatedFirstFiniteCorrect : Targets.EncodedCompensatedFirstFiniteCorrect := by
  intro c a
  let n := rawNoteEncode a.1
  let C := actualControlledCount (compensatedPrefixControl c) a.1.repr
  have hs := actualControlledTraceFirstFinite (compensatedPrefixControl c) a.1.repr (normalRepresentationSound a)
  have ht := encodedCompensatedTrajectoryCorrect c a C le_rfl
  let z : NONote := ⟨rawNoteDecode (encodedCompensatedState c n C),ht.1⟩
  have hzcode : rawNoteEncode z.1=encodedCompensatedState c n C := rawNoteEncodeDecode _
  have hf := (encodedFiniteCorrect z).1.mpr (by rw [ht.2]; exact hs.1)
  rw [hzcode] at hf
  apply Nat.mem_rfind.mpr
  constructor
  · exact Part.mem_some_iff.mpr hf.symm
  · intro k hk
    have htraj := encodedCompensatedTrajectoryCorrect c a k hk.le
    let r : NONote := ⟨rawNoteDecode (encodedCompensatedState c n k),htraj.1⟩
    have hrcode : rawNoteEncode r.1=encodedCompensatedState c n k := rawNoteEncodeDecode _
    have hnon := (hs.2 k hk.le).2.2 hk
    have hfalse : encodedFiniteTest (encodedCompensatedState c n k)=false := by
      cases h : encodedFiniteTest (encodedCompensatedState c n k) with
      | false => rfl
      | true =>
        have hh := (encodedFiniteCorrect r).1.mp (by rw [hrcode]; exact h)
        rw [htraj.2] at hh
        exact ((not_lt_of_ge hnon) hh).elim
    exact Part.mem_some_iff.mpr hfalse.symm

private theorem compensated_count_mem_program (c : Nat) (a : NONote) :
    actualControlledCount (compensatedPrefixControl c) a.1.repr ∈
      encodedCompensatedCountPartial c (rawNoteEncode a.1) := by
  have hn : rawNormalCode (rawNoteEncode a.1)=1 := (rawNormalCorrect a.1).mpr a.2
  rw [encodedCompensatedCountPartial,if_pos hn]
  exact encodedCompensatedFirstFiniteCorrect c a

theorem encodedCompensatedCountPartialRecursive : Targets.EncodedCompensatedCountPartialRecursive := by
  have hi := encodedCompensatedStatePrimitiveRecursive
  have ht : Primrec encodedFiniteTest := encodedFiniteAlgorithmsPrimitiveRecursive.1
  have hp : Primrec (fun p : (Nat × Nat) × Nat => encodedFiniteTest (encodedCompensatedState p.1.1 p.1.2 p.2)) := ht.comp hi
  have hsearch : Partrec (fun p : Nat × Nat => encodedCompensatedSearch p.1 p.2) :=
    Partrec.rfind hp.to_comp.partrec.to₂
  have hn : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hguard : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.2=1) :=
    Primrec.eq.comp (hn.comp Primrec.snd) (Primrec.const 1)
  let flag : Nat × Nat → Nat := fun p => if rawNormalCode p.2=1 then 1 else 0
  have hflag : Computable flag := (Primrec.ite hguard (Primrec.const 1) (Primrec.const 0)).to_comp
  have hbranch : Partrec (fun p : (Nat × Nat) × Nat => encodedCompensatedSearch p.1.1 p.1.2) :=
    hsearch.comp Computable.fst
  exact (Partrec.nat_casesOn_right hflag (Computable.const 0) hbranch.to₂).of_eq (fun p => by
    by_cases h : rawNormalCode p.2=1 <;> simp [flag,h,encodedCompensatedCountPartial])

theorem encodedCompensatedCountTotal : Targets.EncodedCompensatedCountTotal := by
  intro c n
  by_cases hn : rawNormalCode n=1
  · let a : NONote := ⟨rawNoteDecode n,(rawNormalDecodeCorrect n).mp hn⟩
    have hm := compensated_count_mem_program c a
    rw [rawNoteEncodeDecode n] at hm
    exact hm.1
  · simp [encodedCompensatedCountPartial,hn]

theorem encodedCompensatedCountCorrect : Targets.EncodedCompensatedCountCorrect := by
  intro c a
  classical
  have hm := compensated_count_mem_program c a
  unfold encodedCompensatedCountValue
  exact (Part.getOrElse_of_dom _ hm.1 0).trans (Part.get_eq_of_mem hm hm.1)

theorem encodedCompensatedCountComputable : Targets.EncodedCompensatedCountComputable := by
  apply encodedCompensatedCountPartialRecursive.of_eq_tot
  intro p
  classical
  unfold encodedCompensatedCountValue
  rw [Part.getOrElse_of_dom _ (encodedCompensatedCountTotal p.1 p.2) 0]
  exact Part.get_mem (encodedCompensatedCountTotal p.1 p.2)

end LogicLineages.OrdinalComparison
