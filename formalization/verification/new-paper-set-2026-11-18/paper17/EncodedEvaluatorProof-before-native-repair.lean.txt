module
public import LogicLineages.PermittedControl.TerminalProof
public import LogicLineages.OrdinalComparison.EncodedDescentProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

theorem encodedStep_correct (f : Nat → Nat) (a : NONote) (hnon : Ordinal.omega0 ≤ a.1.repr) :
    ONote.NF (rawNoteDecode (encodedStepWith f (rawNoteEncode a.1))) ∧
    (rawNoteDecode (encodedStepWith f (rawNoteEncode a.1))).repr = descentWith f a.1.repr := by
  have ht : encodedFiniteTest (rawNoteEncode a.1) = false := by
    cases h : encodedFiniteTest (rawNoteEncode a.1) with
    | false => rfl
    | true => exact False.elim ((not_lt_of_ge hnon) ((encodedFiniteCorrect a).1.mp h))
  let l : NONote := ⟨rawNoteDecode (rawSplitCode (rawNoteEncode a.1)).unpair.1, rawSplitNormal a⟩
  have hlrepr : l.1.repr = actualLimitPart a.1.repr := (rawSplitActualCorrect a).1
  have hlpos : 0 < l := by
    change 0 < l.1.repr
    rw [hlrepr]
    exact (actualNonfiniteDecomposition a.1.repr hnon (normalRepresentationSound a)).2.1.bot_lt
  have hlcode : rawNoteEncode l.1 = (rawSplitCode (rawNoteEncode a.1)).unpair.1 :=
    rawNoteEncodeDecode _
  have hnorm : rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr := by
    rw [rawNormCodeCorrect a.1, actualOrdinalNorm_notationCorrespondence a]
  have hM := encodedMaximumPredecessorCorrect l hlpos (f (rawNormCode (rawNoteEncode a.1)))
  rw [hlcode] at hM
  simp only [encodedStepWith, ht, Bool.false_eq_true, ↓reduceIte]
  rw [hM, rawNoteDecodeEncode (maximumPredecessor l (f (rawNormCode (rawNoteEncode a.1)))).1]
  refine ⟨(maximumPredecessor l (f (rawNormCode (rawNoteEncode a.1)))).2, ?_⟩
  rw [actualMaximumPredecessor_notationCorrespondence l hlpos _, hlrepr, hnorm, descentWith]


theorem encodedStep_computable (f : Nat → Nat) (hf : Computable f) : Computable (encodedStepWith f) := by
  have hs : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hl := (Primrec.fst.comp (Primrec.unpair.comp hs)).to_comp
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hM := encodedMaximumPredecessorPrimitiveRecursive.to_comp
  have ht := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp
  exact (Computable.cond ht Computable.id (hM.comp hl (hf.comp hn.to_comp))).of_eq
    (fun n => by cases h : encodedFiniteTest n <;> simp [encodedStepWith, h])

theorem encodedStates_computable (f : Nat → Nat) (hf : Computable f) : Computable₂ (encodedStatesWith f) := by
  have hs := encodedStep_computable f hf
  have hstep : Computable₂ (fun (_ : Nat × Nat) (v : Nat × Nat) => encodedStepWith f v.2) :=
    hs.comp (Computable.snd.comp Computable.snd)
  apply (Computable.nat_rec Computable.snd Computable.fst hstep).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ k ih => simpa only [Nat.rec_add_one, encodedStatesWith, Function.iterate_succ_apply', ih]

theorem trajectory_correct (f : Nat → Nat) (a : NONote) (k : Nat) :
    k ≤ (terminalWith f a.1.repr).2 →
    ONote.NF (rawNoteDecode (encodedStatesWith f (rawNoteEncode a.1) k)) ∧
    (rawNoteDecode (encodedStatesWith f (rawNoteEncode a.1) k)).repr = (descentWith f)^[k] a.1.repr := by
  induction k with
  | zero =>
      intro _
      change ONote.NF (rawNoteDecode (rawNoteEncode a.1)) ∧
        (rawNoteDecode (rawNoteEncode a.1)).repr = a.1.repr
      rw [rawNoteDecodeEncode a.1]
      exact ⟨a.2, rfl⟩
  | succ k ih =>
      intro hk
      have hlt : k < (terminalWith f a.1.repr).2 := by omega
      have hp := ih (by omega)
      let r : NONote := ⟨rawNoteDecode (encodedStatesWith f (rawNoteEncode a.1) k), hp.1⟩
      have hr : Ordinal.omega0 ≤ r.1.repr := by
        rw [hp.2]
        exact (terminal_firstFinite f a.1.repr (normalRepresentationSound a)).2 k hlt
      have hs := encodedStep_correct f r hr
      rw [rawNoteEncodeDecode (encodedStatesWith f (rawNoteEncode a.1) k)] at hs
      have hnext : encodedStatesWith f (rawNoteEncode a.1) (k + 1) =
          encodedStepWith f (encodedStatesWith f (rawNoteEncode a.1) k) := by
        simp only [encodedStatesWith, Function.iterate_succ_apply']
      rw [hnext]
      refine ⟨hs.1, ?_⟩
      rw [hs.2, hp.2, Function.iterate_succ_apply']

theorem firstFinite_correct (f : Nat → Nat) (a : NONote) :
    (terminalWith f a.1.repr).2 ∈ terminalSearchWith f (rawNoteEncode a.1) ∧
    encodedFiniteValue (encodedStatesWith f (rawNoteEncode a.1) (terminalWith f a.1.repr).2) = (terminalWith f a.1.repr).1 := by
  let c := rawNoteEncode a.1
  let t := (terminalWith f a.1.repr).2
  have hs := terminal_firstFinite f a.1.repr (normalRepresentationSound a)
  have ht := trajectory_correct f a t le_rfl
  let z : NONote := ⟨rawNoteDecode (encodedStatesWith f c t), ht.1⟩
  have hz : z.1.repr = ((terminalWith f a.1.repr).1 : Ordinal) := ht.2.trans hs.1
  have hzcode : rawNoteEncode z.1 = encodedStatesWith f c t := rawNoteEncodeDecode _
  have hf := (encodedFiniteCorrect z).1.mpr (by
    rw [hz]
    exact Ordinal.natCast_lt_omega0 _)
  rw [hzcode] at hf
  have hsearch : t ∈ terminalSearchWith f c := by
    apply Nat.mem_rfind.mpr
    constructor
    · exact Part.mem_some_iff.mpr hf.symm
    · intro m hm
      have hmtraj := trajectory_correct f a m hm.le
      let r : NONote := ⟨rawNoteDecode (encodedStatesWith f c m), hmtraj.1⟩
      have hrcode : rawNoteEncode r.1 = encodedStatesWith f c m := rawNoteEncodeDecode _
      have hnon := hs.2 m hm
      have hfalse : encodedFiniteTest (encodedStatesWith f c m) = false := by
        cases h : encodedFiniteTest (encodedStatesWith f c m) with
        | false => rfl
        | true =>
            have hfinite : r.1.repr < Ordinal.omega0 := (encodedFiniteCorrect r).1.mp (by
              rw [hrcode]
              exact h)
            have hfinite' : ((descentWith f)^[m]) a.1.repr < Ordinal.omega0 := by
              rw [← hmtraj.2]
              exact hfinite
            exact False.elim ((not_lt_of_ge hnon) hfinite')
      exact Part.mem_some_iff.mpr hfalse.symm
  refine ⟨hsearch, ?_⟩
  have hv := (encodedFiniteCorrect z).2 (by rw [hzcode]; exact hf)
  rw [hzcode, hz] at hv
  exact_mod_cast hv

theorem collapse_mem_program (f : Nat → Nat) (hmono : StrictMono f) (hf : ∀ n, G n ≤ f n) (a : NONote) :
    collapseWith f a.1.repr ∈ evaluatorPartialWith f (rawNoteEncode a.1) := by
  have hn : rawNormalCode (rawNoteEncode a.1) = 1 := (rawNormalCorrect a.1).mpr a.2
  rw [evaluatorPartialWith, if_pos hn]
  have hs := firstFinite_correct f a
  have hm := Part.mem_map (fun k => encodedFiniteValue (encodedStatesWith f (rawNoteEncode a.1) k) + k) hs.1
  rw [hs.2, ← (terminal_identities f hmono hf a.1.repr (normalRepresentationSound a)).1] at hm
  exact hm

theorem evaluator_partrec (f : Nat → Nat) (hf : Computable f) : Partrec (evaluatorPartialWith f) := by
  have hi := encodedStates_computable f hf
  have ht := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp
  have hv : Computable encodedFiniteValue :=
    (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).to_comp
  have hp : Computable (fun p : Nat × Nat => encodedFiniteTest (encodedStatesWith f p.1 p.2)) := ht.comp hi
  have hsearch : Partrec (terminalSearchWith f) := Partrec.rfind hp.partrec.to₂
  have hresult : Computable (fun p : Nat × Nat => encodedFiniteValue (encodedStatesWith f p.1 p.2) + p.2) :=
    Primrec.nat_add.to_comp.comp (hv.comp hi) Computable.snd
  have hbranch : Partrec (fun n => (terminalSearchWith f n).map
      (fun k => encodedFiniteValue (encodedStatesWith f n k) + k)) := hsearch.map hresult.to₂
  have hn : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hguard : PrimrecPred (fun n : Nat => rawNormalCode n = 1) :=
    Primrec.eq.comp hn (Primrec.const 1)
  let flag : Nat → Nat := fun n => if rawNormalCode n = 1 then 1 else 0
  have hflag : Computable flag := (Primrec.ite hguard (Primrec.const 1) (Primrec.const 0)).to_comp
  have hbranchPair : Partrec (fun p : Nat × Nat => (terminalSearchWith f p.1).map
      (fun k => encodedFiniteValue (encodedStatesWith f p.1 k) + k)) := hbranch.comp Computable.fst
  exact (Partrec.nat_casesOn_right hflag (Computable.const 0) hbranchPair.to₂).of_eq (fun n => by
    by_cases h : rawNormalCode n = 1 <;> simp [flag, h, evaluatorPartialWith])

theorem evaluator_total (f : Nat → Nat) (hmono : StrictMono f) (hf : ∀ n, G n ≤ f n)
    (n : Nat) : (evaluatorPartialWith f n).Dom := by
  by_cases hn : rawNormalCode n = 1
  · let a : NONote := ⟨rawNoteDecode n, (rawNormalDecodeCorrect n).mp hn⟩
    have hm := collapse_mem_program f hmono hf a
    rw [rawNoteEncodeDecode n] at hm
    exact hm.1
  · simp [evaluatorPartialWith, hn]

theorem evaluator_computable (f : Nat → Nat) (hc : Computable f) (hmono : StrictMono f)
    (hf : ∀ n, G n ≤ f n) : Computable (evaluatorWith f) := by
  apply (evaluator_partrec f hc).of_eq_tot
  intro n
  classical
  unfold evaluatorWith
  rw [Part.getOrElse_of_dom _ (evaluator_total f hmono hf n) 0]
  exact Part.get_mem (evaluator_total f hmono hf n)

theorem evaluator_source (f : Nat → Nat) (hmono : StrictMono f) (hf : ∀ n, G n ≤ f n)
    (a : NONote) : evaluatorWith f (rawNoteEncode a.1) = collapseWith f a.1.repr := by
  classical
  have hm := collapse_mem_program f hmono hf a
  unfold evaluatorWith
  exact (Part.getOrElse_of_dom _ hm.1 0).trans (Part.get_eq_of_mem hm hm.1)

theorem computableEvaluation : Targets.ComputableEvaluation := by
  intro f hc hmono hf
  exact ⟨terminalSemantics f hmono hf, firstFinite_correct f, evaluator_partrec f hc,
    evaluator_total f hmono hf, evaluator_computable f hc hmono hf, evaluator_source f hmono hf⟩

theorem selectedClosedEvaluation : Targets.SelectedClosedEvaluation := by
  constructor
  · exact computableEvaluation factorialControl factorialControl_primrec.to_comp
      selectedControlAdmissibility.1.1 selectedControlAdmissibility.1.2
  · intro b
    exact computableEvaluation (nearControl b)
      (nearControl_primrec.comp (Primrec.const b) Primrec.id).to_comp
      (selectedControlAdmissibility.2 b).1 (selectedControlAdmissibility.2 b).2

end LogicLineages.PermittedControl
