module
public import LogicLineages.OrdinalComparison.PeakWordProgramBlocksProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PeakWordProgram

private theorem state_step_primitive : Primrec₂ encodedPrincipalKernelStateStep := by
  have hc : Primrec (fun p : (Nat × List (Nat × Nat)) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : (Nat × List (Nat × Nat)) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have he : Primrec (fun p : (Nat × List (Nat × Nat)) × Nat => p.2) := Primrec.snd
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact (Primrec.nat_add.comp hc (Primrec.nat_add.comp (Primrec.const 1) (hn.comp he))).pair
    (Primrec.list_cons.comp (he.pair hc) hw)

private theorem word_primitive : Primrec₂ encodedPrincipalWordFromBlocks := by
  have hs : Primrec₂ (fun _ : List Nat × Nat => fun p : (Nat × List (Nat × Nat)) × Nat =>
      encodedPrincipalKernelStateStep p.1 p.2) := state_step_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.snd.comp (Primrec.list_foldl (f := fun p : List Nat × Nat => p.1)
    (g := fun p => (p.2,([] : List (Nat × Nat))))
    (h := fun _ p => encodedPrincipalKernelStateStep p.1 p.2)
    Primrec.fst (Primrec.snd.pair (Primrec.const [])) hs)

private theorem fold_word (es : List ONote) (c : Nat) (w : List (Nat × Nat)) :
    ((es.map rawNoteEncode).foldl encodedPrincipalKernelStateStep (c,w)).2=
      encodePrincipalKernelWord (principalKernelWord es c)++w := by
  induction es generalizing c w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.foldl_cons,encodedPrincipalKernelStateStep,rawNormCodeCorrect]
    rw [ih]
    simp only [principalKernelWord,encodePrincipalKernelWord,List.map_append,List.map_singleton,List.append_assoc,List.singleton_append]
    rw [rawNormCodeCorrect e]

theorem word : Targets.PrincipalWordCodeProgram := by
  refine ⟨word_primitive,fun es c => ?_⟩
  simpa only [encodedPrincipalWordFromBlocks,List.append_nil] using fold_word es c []

theorem peak : Targets.PrincipalPeakWordCodeProgram := by
  refine ⟨word.1.comp blocks.1 (Primrec.const 0),fun o => ?_⟩
  simp only [encodedPrincipalPeakWord,blocks.2,word.2]

theorem full : Targets.FullPrincipalPeakWordCodeProgram := ⟨blocks,word,peak⟩

end LogicLineages.OrdinalComparison.PeakWordProgram
