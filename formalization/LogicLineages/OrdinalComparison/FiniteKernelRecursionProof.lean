module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelsProof
public import LogicLineages.OrdinalComparison.SignedKernelDomainProof
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteKernelRecursion

private theorem power_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
  simpa only [Nat.cast_one,mul_one,Nat.mul_one] using
    (actualFiniteMonomialFacts d 1).2.1

private theorem next_power (n : Nat) :
    Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0 =
      Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal) := by
  rw [← Ordinal.opow_add_one]
  congr 1

theorem block : Targets.ActualFiniteKernelBlockRecursion := by
  intro n c t ht
  dsimp only
  have hpos : (0 : Ordinal) < ((n+1 : Nat) : Ordinal) := by
    exact_mod_cast (by omega : 0 < n+1)
  have heps : Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0 < epsilonZero := by
    rw [next_power]
    exact finiteOmegaPowerBelowEpsilonZero (n+2)
  have hn : actualOrdinalNorm
      (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0) = n+3 := by
    rw [next_power,power_norm]
  have hdom : c + actualOrdinalNorm (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)) +
      actualOrdinalNorm (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0) ≤ t := by
    rw [power_norm,hn]
    omega
  have hc := actualSuccessorCountCocycle ((n+1 : Nat) : Ordinal) hpos heps c t hdom
  have hv := actualSuccessorKernelComposition ((n+1 : Nat) : Ordinal) hpos heps c t hdom
  rw [next_power,power_norm] at hc hv
  constructor
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv

private theorem entry_self_le (n c t : Nat) :
    t ≤ actualSuffixKernel (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t := by
  exact iterate_self_le (fun x => (self_lt_Phi x).le) _ t

private theorem signed_positive (d c : Nat) (j : Int) (t : Nat)
    (hd : 2 ≤ d ∨ (d=1 ∧ 0 ≤ j))
    (hdom : c+d+1 ≤ t) (hlarge : c+2*j.natAbs+3 ≤ t) :
    0 < signedKernelDepth d c j t := by
  rcases hd with hd | ⟨rfl,hj⟩
  · have hcount := SignedKernelDomainProof.finiteDegreeCounterLowerBound.2 d c j.natAbs t hd
      (max_le hdom hlarge)
    have hj : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
    dsimp only [signedKernelDepth]
    omega
  · exact (SignedKernelDomainProof.degreeOneSignedDomain c t (by omega) j).2.mpr hj

theorem signed_block : Targets.ActualFiniteSignedBlockRecursion := by
  intro n c j hj t ht
  dsimp only
  let entry := actualSuffixKernel (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t
  have hdom : c+2*(n+2)+1 ≤ t := (Nat.le_max_left _ _).trans ht
  have hlarge : c+2*j.natAbs+3 ≤ t := (Nat.le_max_right _ _).trans ht
  have hentry : t ≤ entry := entry_self_le n c t
  have hchild : 2 ≤ n+1 ∨ (n+1=1 ∧ 0 ≤ j) := by omega
  have hp := signed_positive (n+2) c j t (Or.inl (by omega)) (by omega) hlarge
  have hc := signed_positive (n+1) c j entry hchild (by omega) (by omega)
  refine ⟨hp,hc,?_⟩
  have he := (block n c t hdom).1
  change actualSuffixKernelCount (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) c t =
    actualSuffixKernelCount (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)) c entry +
      actualSuffixKernelCount (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t at he
  have hdepth : (signedKernelDepth (n+2) c j t).toNat =
      (signedKernelDepth (n+1) c j entry).toNat +
        actualSuffixKernelCount (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t := by
    dsimp only [signedKernelDepth] at hp hc ⊢
    omega
  unfold rawSignedKernelValue
  rw [hdepth,Function.iterate_add_apply]
  rfl

theorem quadratic : Targets.ActualFiniteQuadraticShift := by
  intro c t ht j
  have hcount := actualOmegaSquaredSuffixCount c t ht
  have hg := self_lt_Phi t
  have hsub : (c+1)/2 ≤ Phi t/2 := by omega
  have hdepth : signedKernelDepth 2 c j t =
      ((Phi t / 2 : Nat) : Int) + (j - (((c+1)/2 : Nat) : Int)) + 1 := by
    dsimp only [signedKernelDepth]
    simp only [Nat.cast_ofNat] at *
    rw [hcount]
    omega
  refine ⟨hdepth,?_⟩
  simp only [rawSignedKernelValue,hdepth,rawQuadraticShift]

attribute [local irreducible] Nat.sqrt Nat.unpair encodedSuffixKernelCount encodedSuffixKernelValue encodedNatNote

theorem programs : Targets.ActualFiniteKernelPrograms := by
  have hargs : Primrec (fun p : Nat × Nat × Nat => (encodedNatNote p.1,p.2.1,p.2.2)) :=
    (encodedKernelBuildersPrimitiveRecursive.1.comp Primrec.fst).pair Primrec.snd
  have hc : Computable (fun p : Nat × Nat × Nat => encodedSuffixKernelCount p.1 p.2.1 p.2.2) :=
    encodedSuffixKernelComputable.1
  have hv : Computable (fun p : Nat × Nat × Nat => encodedSuffixKernelValue p.1 p.2.1 p.2.2) :=
    encodedSuffixKernelComputable.2
  have hcode : Computable (fun p : Nat × Nat × Nat =>
      encodedSuffixKernelCount (encodedNatNote p.1) p.2.1 p.2.2) := Computable.comp hc hargs.to_comp
  have hvalue : Computable (fun p : Nat × Nat × Nat =>
      encodedSuffixKernelValue (encodedNatNote p.1) p.2.1 p.2.2) := Computable.comp hv hargs.to_comp
  refine ⟨?_,?_,?_⟩
  · change Computable (fun p : Nat × Nat × Nat =>
      encodedSuffixKernelCount (encodedNatNote p.1) p.2.1 p.2.2)
    exact hcode
  · change Computable (fun p : Nat × Nat × Nat =>
      encodedSuffixKernelValue (encodedNatNote p.1) p.2.1 p.2.2)
    exact hvalue
  intro d c t hd ht
  let eta : NONote := ⟨ONote.ofNat d,ONote.nf_ofNat d⟩
  have hpos : 0 < eta.1.repr := by
    simp only [eta,ONote.repr_ofNat]
    exact_mod_cast (by omega : 0 < d)
  have hdom : c+actualOrdinalNorm (Ordinal.omega0 ^ eta.1.repr) ≤ t := by
    simp only [eta,ONote.repr_ofNat,power_norm]
    exact ht
  have h := encodedSuffixKernelCorrect eta hpos c t hdom
  change encodedSuffixKernelCount (encodedNatNote d) c t = _ ∧
    encodedSuffixKernelValue (encodedNatNote d) c t = _
  rw [encodedNatNoteCorrect d]
  simpa only [eta,ONote.repr_ofNat] using h

theorem obstruction : Targets.ActualSignedDegreeTwoRecursionObstruction := by
  refine ⟨?_,?_,?_⟩
  · intro c t ht
    have h := (SignedKernelDomainProof.degreeOneSignedDomain c t ht (-1)).1
    simpa using h
  · intro c t ht
    apply signed_positive 2 c (-1) t (Or.inl le_rfl)
    · have h := (Nat.le_max_left _ _).trans ht
      change c+2*2+1 ≤ t at h
      omega
    · exact (Nat.le_max_right _ _).trans ht
  · intro c
    exact SignedKernelDomainProof.degreeOneNegativeDepthObstruction c (-1) (by norm_num)

end LogicLineages.OrdinalComparison.FiniteKernelRecursion
