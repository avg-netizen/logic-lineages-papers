module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Exact quadratic value from the already checked count formula, avoiding
an unrelated linked-residue import in the older aggregate signed supplier. -/
private theorem quadratic_value (c t : Nat) (ht : c+3 ≤ t) (j : Int) :
    rawSignedKernelValue 2 c j t = rawQuadraticShift (j-(((c+1)/2 : Nat) : Int)) t := by
  have hcount := CounterLeaderExpansion.Proof.quadraticCount c t ht
  have hg := self_lt_Phi t
  have hsub : (c+1)/2 ≤ Phi t/2 := by omega
  have hdepth : signedKernelDepth 2 c j t =
      ((Phi t/2 : Nat) : Int)+(j-(((c+1)/2 : Nat) : Int))+1 := by
    dsimp only [signedKernelDepth]
    simp only [Nat.cast_ofNat] at *
    rw [hcount]
    omega
  simp only [rawSignedKernelValue,hdepth,rawQuadraticShift]

theorem expansionSyntax : Targets.ExpansionSyntax := by
  intro D n c j hD
  have hLower : LetterAllowed D (lowerHead n c j) := by
    cases n with
    | zero => simp [lowerHead,quadraticLetter,LetterAllowed]
    | succ n => simp [lowerHead,kernelLetter,LetterAllowed]; omega
  refine ⟨?_,rfl,?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [kernelLetter,LetterAllowed,hD]
    · have he := List.mem_singleton.mp ha
      subst a
      exact hLower
  · cases n <;> simp [expansionWord,lowerHead,counterNodes,kernelLetter,quadraticLetter]

/-- The original source schedules are converted only after paying their
separate parent, retained-inner and reached-child bridge thresholds. -/
theorem sourceBlockExpansion : Targets.SourceBlockExpansion := by
  intro D n c t j hD ht
  have hrec : finiteKernelRecursionThreshold (n+3) c j ≤ t := (Nat.le_max_left _ _).trans ht
  have hbridge : c+2*(n+3)+1 ≤ t := (Nat.le_max_left _ _).trans hrec
  have hOrig : LetterAllowed D (kernelLetter (n+3) c j) := by
    simp [kernelLetter,LetterAllowed,hD]
  have hDom := WordGuardCompletion.Proof.letterTailCorrect D (kernelLetter (n+3) c j) t hOrig
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht))
  have hNew := WordGuardCompletion.Proof.wordTailCorrect D (expansionWord n c j) t
    (expansionSyntax D n c j hD).1
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ht))
  let entry := actualSuffixKernel (Ordinal.omega0 ^ ((n+3 : Nat) : Ordinal)) (c+(n+3)) t
  have hEntry : t ≤ entry := iterate_self_le (fun z => (self_lt_Phi z).le) _ t
  have hParentBridge := Focused.sourceProcessBridge (n+3) c t (by omega) (by omega)
  have hInnerBridge := Focused.sourceProcessBridge (n+3) (c+(n+3)) t (by omega) (by omega)
  have hChildBridge := Focused.sourceProcessBridge (n+2) c entry (by omega) (by omega)
  have hParent : sourceSignedValue (n+3) c j t = rawSignedKernelValue (n+3) c j t := by
    simp only [sourceSignedValue,sourceSignedDepth,rawSignedKernelValue,signedKernelDepth,hParentBridge.1]
  have hInner : sourceSignedValue (n+3) (c+(n+3)) 0 t = entry := by
    simpa [sourceSignedValue,sourceSignedDepth,sourceValue,entry] using hInnerBridge.2.1
  have hChild : sourceSignedValue (n+2) c j entry = rawSignedKernelValue (n+2) c j entry := by
    simp only [sourceSignedValue,sourceSignedDepth,rawSignedKernelValue,signedKernelDepth,hChildBridge.1]
  have hBlockCount := (CounterLeaderExpansion.Proof.block (n+1) c t
    (by simpa only [Nat.add_assoc] using hbridge)).1
  have hCount : actualSuffixKernelCount (Ordinal.omega0 ^ ((n+3 : Nat) : Ordinal)) c t =
      actualSuffixKernelCount (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) c entry+
        actualSuffixKernelCount (Ordinal.omega0 ^ ((n+3 : Nat) : Ordinal)) (c+(n+3)) t := by
    simpa only [entry,Nat.add_assoc] using hBlockCount
  have hj : -(j.natAbs : Int) ≤ j := by omega
  have hlarge : c+2*j.natAbs+3 ≤ t := (Nat.le_max_right _ _).trans hrec
  have hChildLower := WordGuardCompletion.Proof.sourceCount_lower (n+2) c entry (by omega) (by omega)
  have hParentPos : 0 < signedKernelDepth (n+3) c j t := by
    have hp : 0 < sourceSignedDepth (n+3) c j t := hDom.1.2
    simpa only [sourceSignedDepth,signedKernelDepth,hParentBridge.1] using hp
  have hChildPos : 0 < signedKernelDepth (n+2) c j entry := by
    unfold signedKernelDepth
    rw [←hChildBridge.1]
    omega
  have hDepth : (signedKernelDepth (n+3) c j t).toNat =
      (signedKernelDepth (n+2) c j entry).toNat+
        actualSuffixKernelCount (Ordinal.omega0 ^ ((n+3 : Nat) : Ordinal)) (c+(n+3)) t := by
    unfold signedKernelDepth at hParentPos hChildPos ⊢
    rw [hCount]
    omega
  have hBlock : rawSignedKernelValue (n+3) c j t = rawSignedKernelValue (n+2) c j entry := by
    unfold rawSignedKernelValue
    rw [hDepth,Function.iterate_add_apply]
    rfl
  have hLower : rawSignedKernelValue (n+2) c j entry = letterValue (lowerHead n c j) entry := by
    cases n with
    | zero =>
        change rawSignedKernelValue 2 c j entry = rawQuadraticShift (j-(((c+1)/2 : Nat) : Int)) entry
        exact quadratic_value c entry (by omega) j
    | succ n =>
        change rawSignedKernelValue (n+1+2) c j entry = sourceSignedValue (n+1+2) c j entry
        exact hChild.symm
  refine ⟨hDom.1,hNew.1,?_⟩
  rw [hParent,hBlock,hLower]
  change letterValue (lowerHead n c j) entry =
    letterValue (lowerHead n c j) (sourceSignedValue (n+3) (c+(n+3)) 0 t)
  rw [hInner]

end LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
