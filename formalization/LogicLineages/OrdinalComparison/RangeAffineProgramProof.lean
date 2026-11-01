module
public import LogicLineages.OrdinalComparison.RangeAffineProgramTargets
public import LogicLineages.OrdinalComparison.OneVariableComparisonProgramProof
public import LogicLineages.OrdinalComparison.AdjacentProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeAffineProgram

private theorem principal_below (eta : NONote) : Ordinal.omega0^eta.1.repr<epsilonZero := by
  letI := eta.2
  let L : NONote := ⟨ONote.oadd eta.1 1 0,inferInstance⟩
  simpa [L,ONote.repr] using normalRepresentationSound L

private theorem kernel_phi_lower (eta : NONote) (hp : 0<eta.1.repr) (c t : Nat)
    (hd : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t) :
    Phi t≤actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t := by
  have hpos := (actualSuffixKernelTrace eta.1.repr hp (principal_below eta) c t hd).1
  let n := actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) c t
  have hn : n=(n-1)+1 := by change 0<n at hpos; omega
  calc
    Phi t≤Phi ((Phi^[n-1]) t) :=
      Phi_strictMono.monotone (iterate_self_le (fun x => (self_lt_Phi x).le) _ _)
    _ = actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t := by
      change Phi ((Phi^[n-1]) t)=(Phi^[n]) t
      conv_rhs => rw [hn,Function.iterate_succ_apply']

theorem range_phi_lower : Targets.ActualSourceRangePhiLowerBound := by
  intro w E hv x hx
  cases w with
  | nil => exact (hv.1 rfl).elim
  | cons p rest =>
    rcases p with ⟨eta,c⟩
    have hop := OneVariableComparison.open_lower E hv.2.2.1 hv.2.2.2 x
    have hdom := OneVariableComparison.word_domains ((eta,c)::rest) _ (hx.trans hop)
    have hp : 0<eta.1.repr := hv.2.1 (eta,c) (by simp)
    have hK := kernel_phi_lower eta hp c _ hdom.1.1
    have hrestbound : comparisonWordDomainBound rest≤x := (Nat.le_max_right _ _).trans hx
    have hrest := OneVariableComparison.word_domains rest
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c (actualFixedLimitProfileEval E x))
      (hrestbound.trans (hop.trans (OneVariableComparison.kernel_expansive (Ordinal.omega0^eta.1.repr) c _)))
    change Phi x≤(actualPrincipalWordRun (comparisonRawWord rest)
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c (actualFixedLimitProfileEval E x))).1
    exact (Phi_strictMono.monotone hop).trans (hK.trans hrest.2)

private theorem affine_phi (a b x : Nat) (h4 : 4≤x) (hab : a+b+3≤x) : a*x+b<Phi x := by
  -- The omega affine supplier asks for 4, while x=4 can leave x-1=3.
  -- In that single small case, the explicit control lower bound suffices.
  by_cases h5 : 5≤x
  · have hh := actualOmegaAffineCrossMassSeparation a b (x-1) x 0 0
      (by omega) (by omega) (by omega) (by omega)
    rw [(actualOmegaSuffixKernel 0 (x-1) (by omega)).1,
      (actualOmegaSuffixKernel 0 (x-1) (by omega)).2,
      (actualOmegaSuffixKernel 0 x (by omega)).2] at hh
    have hxin : x≤Phi (x-1)+1 := by have h := self_lt_Phi (x-1); omega
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left a hxin) b).trans_lt (by omega)
  · have hx : x=4 := by omega
    subst x
    have hPhi := two_pow_shift_le_Phi 4
    norm_num at hPhi
    omega

theorem actual_program : Targets.ActualSourceRangeAffineProgram := by
  have hsrc := OneVariableComparison.source_program.1
  have hn : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have ha : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  refine ⟨Primrec.nat_max.comp (hsrc.comp hn)
    (Primrec.nat_max.comp (Primrec.const 4)
      (Primrec.nat_add.comp (Primrec.nat_add.comp ha hb) (Primrec.const 3))),?_⟩
  intro w E hv a b
  have hs := OneVariableComparison.source_program.2.2 (.range w E) hv
  refine ⟨?_,?_⟩
  · unfold encodedRangeAffineTail
    omega
  · intro x hx
    have hdom : oneVariableComparisonDomainBound (.range w E)≤x := by
      rw [← hs.1]
      exact (Nat.le_max_left _ _).trans hx
    have h4 : 4≤x := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hx)
    have hab : a+b+3≤x := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hx)
    exact ⟨(hs.2.2 x hdom).1,(affine_phi a b x h4 hab).trans_le (range_phi_lower w E hv x hdom)⟩

end LogicLineages.OrdinalComparison.RangeAffineProgram
