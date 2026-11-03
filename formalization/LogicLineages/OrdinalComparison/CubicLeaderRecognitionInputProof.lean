module
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionTargets
public import LogicLineages.OrdinalComparison.AdjacentReserveCutProof
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof

/-! The identity-profile case needs only the retained finite tail, rather than
the full profile-reserve theorem or the linked-residue development. -/

private noncomputable def input_packed_state (L : NONote) (t c e : Nat) : Ordinal :=
  let B := Phi t
  let B' := Phi (t+1)
  let b := actualMaximumPredecessor L.1.repr (B-e)
  let pi := (profileLeadingNote (maximumPredecessor L (B-e))).1.repr
  let R := profileReserveBlocks (profileBoundWord .input)
  let p := c+R*actualOrdinalNorm pi
  let k := (B'+e)-(B+p)
  pi*(R : Ordinal)+(b+(k : Ordinal))

private theorem input_packed_facts (L : NONote)
    (hp : ∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell)
    (hlarge : Ordinal.omega0 < L.1.repr) (t c e : Nat)
    (hT : profileAdjacentThreshold L .input ≤ t)
    (hc : c + actualOrdinalNorm L.1.repr ≤ t+1)
    (he : e + actualOrdinalNorm L.1.repr ≤ t) :
    input_packed_state L t c e < epsilonZero ∧
    input_packed_state L t c e ≤ actualMaximumPredecessor L.1.repr (Phi (t+1)-c) ∧
    actualOrdinalNorm (input_packed_state L t c e) =
      actualOrdinalNorm (actualMaximumPredecessor L.1.repr (Phi (t+1)-c)) := by
  have hpack := actualAdjacentPackedState L hp hlarge .input True.intro t c e hT hc he
  exact ⟨hpack.2.2.2.2.1.trans (normalRepresentationSound L),
    hpack.2.2.2.2.2.2.2.2.2.1,
    hpack.2.2.2.2.2.2.2.2.1.trans hpack.2.2.2.2.2.2.2.2.2.2.symm⟩

private theorem finite_tail_exit_lower (pref : Ordinal) (he : pref < epsilonZero)
    (c n : Nat) :
    n ≤ c+actualOrdinalNorm
      (actualControlledStateAfter (compensatedPrefixControl c) (pref+(n : Ordinal))
        (actualControlledCount (compensatedPrefixControl c) (pref+(n : Ordinal)))) := by
  have htail := actualFiniteTailClosureNorm pref he n
  have hn := actualControlledNormIteration (compensatedPrefixControl c) (pref+(n : Ordinal))
    htail.1 (actualControlledCount (compensatedPrefixControl c) (pref+(n : Ordinal))) le_rfl
  have hnlow : n ≤ actualOrdinalNorm (pref+(n : Ordinal)) := by
    rw [htail.2]
    exact Nat.le_add_left _ _
  rw [hn]
  exact (hnlow.trans (iterate_self_le
    (fun x => ((compensatedPrefixControlBounds c).2 x).2.le) _ _)).trans (Nat.le_add_left _ _)

private theorem input_cut_lower (L : NONote)
    (hp : ∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell)
    (hlarge : Ordinal.omega0 < L.1.repr) (t c e : Nat)
    (hT : profileAdjacentThreshold L .input ≤ t)
    (hc : c + actualOrdinalNorm L.1.repr ≤ t+1)
    (he : e + actualOrdinalNorm L.1.repr ≤ t) :
    actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t <
      c+actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl c)
        (input_packed_state L t c e)
        (actualControlledCount (compensatedPrefixControl c) (input_packed_state L t c e))) := by
  let B := Phi t
  let B' := Phi (t+1)
  let b := actualMaximumPredecessor L.1.repr (B-e)
  let pi := (profileLeadingNote (maximumPredecessor L (B-e))).1.repr
  let R := profileReserveBlocks (profileBoundWord .input)
  let p := c+R*actualOrdinalNorm pi
  let k := (B'+e)-(B+p)
  let A := input_packed_state L t c e
  let D := actualSuffixKernelCount L.1.repr e t
  let Z := actualSuffixKernel L.1.repr e t
  let q := actualControlledCount (compensatedPrefixControl p) (b+(k : Ordinal))
  let n := (Phi^[q]) B'-p
  let g := compensatedPrefixControl c
  have hcut := actualAdjacentReserveCut L hp hlarge .input True.intro t c e hT hc he
  have hlead := actualAdjacentLeadingCoverage L hp hlarge .input True.intro t e hT he
  have heL := normalRepresentationSound L
  obtain ⟨gamma, _, hpi⟩ := hlead.2.2.2.2.1
  change pi = Ordinal.omega0^gamma at hpi
  have hpieps : Ordinal.omega0^gamma < epsilonZero := by
    rw [← hpi]
    exact hlead.2.2.1.trans heL
  have hprefix : pi*(R : Ordinal) < epsilonZero := by
    rw [hpi]
    exact (reserveStagePrincipalMultipleFacts gamma hpieps R).1
  have hzn : Z+D < n := hcut.2.2.2.2.2.2.2
  have hS : Z+D < c+actualOrdinalNorm
      (actualControlledStateAfter g (pi*(R : Ordinal)+(n : Ordinal))
        (actualControlledCount g (pi*(R : Ordinal)+(n : Ordinal)))) :=
    hzn.trans_le (finite_tail_exit_lower (pi*(R : Ordinal)) hprefix c n)
  have hA : A < epsilonZero := (input_packed_facts L hp hlarge t c e hT hc he).1
  have hendpoint := actualControlledEndpointAlongTrace g A hA q hcut.2.2.1
  have hentry : actualControlledStateAfter g A q = pi*(R : Ordinal)+(n : Ordinal) :=
    hcut.2.2.2.2.2.2.1
  rw [hentry] at hendpoint
  rw [hendpoint] at hS
  exact hS

private theorem input_exit_upper (L : NONote)
    (hp : ∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell)
    (hlarge : Ordinal.omega0 < L.1.repr) (t c e : Nat)
    (hT : profileAdjacentThreshold L .input ≤ t)
    (hc : c + actualOrdinalNorm L.1.repr ≤ t+1)
    (he : e + actualOrdinalNorm L.1.repr ≤ t) :
    c+actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl c)
      (input_packed_state L t c e)
      (actualControlledCount (compensatedPrefixControl c) (input_packed_state L t c e))) ≤
        actualSuffixKernel L.1.repr c (t+1) := by
  let A := input_packed_state L t c e
  let Q := actualMaximumPredecessor L.1.repr (Phi (t+1)-c)
  let g := compensatedPrefixControl c
  have hpack := input_packed_facts L hp hlarge t c e hT hc he
  have heL := normalRepresentationSound L
  have hQ : Q < epsilonZero :=
    (actualMaximumPredecessor_correct L.1.repr (Ordinal.omega0_pos.trans hlarge)
      heL (Phi (t+1)-c)).1.1.trans heL
  have hb := compensatedPrefixControlBounds c
  have hm := actualControlledExitNormMonotone g hb.1 (fun x => (hb.2 x).2.le) A Q
    hpack.2.1 hQ hpack.2.2.le
  obtain ⟨ell, hL⟩ := hp
  have hell : (1 : Ordinal) < ell :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
      rw [Ordinal.opow_one, ← hL]
      exact hlarge)
  have hel : Ordinal.omega0^ell < epsilonZero := by rw [← hL]; exact heL
  have hfirst := actualSuffixKernelFirstMaximum ell (zero_lt_one.trans hell) hel c (t+1)
    (by rw [← hL]; exact hc)
  have hK : actualSuffixKernel L.1.repr c (t+1) = c+actualOrdinalNorm
      (actualControlledStateAfter g Q (actualControlledCount g Q)) := by
    simpa only [← hL] using hfirst.2.2
  exact (Nat.add_le_add_left hm c).trans_eq hK.symm

private theorem adjacent_input (L : NONote)
    (hp : ∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell)
    (hlarge : Ordinal.omega0 < L.1.repr) (t c e : Nat)
    (hT : profileAdjacentThreshold L .input ≤ t)
    (hc : c + actualOrdinalNorm L.1.repr ≤ t+1)
    (he : e + actualOrdinalNorm L.1.repr ≤ t) :
    actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t <
      actualSuffixKernel L.1.repr c (t+1) :=
  (input_cut_lower L hp hlarge t c e hT hc he).trans_le
    (input_exit_upper L hp hlarge t c e hT hc he)

private theorem cross_input (L : NONote)
    (hp : ∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell)
    (hlarge : Ordinal.omega0 < L.1.repr) (t u c e : Nat)
    (hT : profileAdjacentThreshold L .input ≤ t) (htu : t < u)
    (hc : c + actualOrdinalNorm L.1.repr ≤ u)
    (he : e + actualOrdinalNorm L.1.repr ≤ t) :
    actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t <
      actualSuffixKernel L.1.repr c u := by
  let N := actualOrdinalNorm L.1.repr
  have htN : N ≤ t := (Nat.le_add_left _ e).trans he
  have ht1 : N ≤ t+1 := htN.trans (Nat.le_succ t)
  have hu : N ≤ u := htN.trans htu.le
  have hadj := adjacent_input L hp hlarge t (t+1-N) e hT
    (Nat.sub_add_cancel ht1).le he
  obtain ⟨beta, hL⟩ := hp
  have hb : (1 : Ordinal) < beta :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
      rw [Ordinal.opow_one, ← hL]
      exact hlarge)
  have heps : Ordinal.omega0^beta < epsilonZero := by
    rw [← hL]
    exact normalRepresentationSound L
  have hw := actualWorstMassKernelMonotone beta (zero_lt_one.trans hb) heps (t+1) u
    (by rw [← hL]; exact ht1) htu
  have hmass : c ≤ u-N := by omega
  have hm := actualSuffixKernelInputMassMonotone beta (zero_lt_one.trans hb) heps c (u-N) u u
    hmass le_rfl (by rw [← hL]; exact (Nat.sub_add_cancel hu).le)
    (by rw [← hL]; exact hc)
  rw [← hL] at hw hm
  exact hadj.trans_le (hw.trans hm)

private def cubic_note : NONote :=
  ⟨ONote.oadd (ONote.ofNat 3) 1 0,
    ONote.NF.oadd (ONote.nf_ofNat 3) 1 ONote.NFBelow.zero⟩

private theorem cubic_note_repr : cubic_note.1.repr = Ordinal.omega0^(3 : Ordinal) := by
  simp [cubic_note, ONote.repr]

private theorem cubic_norm : actualOrdinalNorm (Ordinal.omega0^(3 : Ordinal)) = 4 := by
  simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
    (actualFiniteMonomialFacts 3 1).2.1

private theorem cubic_input_threshold : profileAdjacentThreshold cubic_note .input = 8 := by
  decide

theorem cubic_strict_inputs (c e t u : Nat)
    (ht : cubicModulus c e ≤ t) (hu : cubicModulus c e ≤ u) (htu : t < u) :
    CounterLeaderExpansion.kernel 3 c t < CounterLeaderExpansion.kernel 3 e u := by
  have hlarge : Ordinal.omega0 < cubic_note.1.repr := by
    rw [cubic_note_repr]
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
        (show (1 : Ordinal) < 3 by norm_num)
  have hT : profileAdjacentThreshold cubic_note .input ≤ t := by
    rw [cubic_input_threshold]
    have hb := (Nat.le_max_left 16 (max c e+4)).trans ht
    omega
  have hc : c+actualOrdinalNorm cubic_note.1.repr ≤ t := by
    rw [cubic_note_repr, cubic_norm]
    have hb := (Nat.le_max_right 16 (max c e+4)).trans ht
    omega
  have he : e+actualOrdinalNorm cubic_note.1.repr ≤ u := by
    rw [cubic_note_repr, cubic_norm]
    have hb := (Nat.le_max_right 16 (max c e+4)).trans hu
    omega
  have h := cross_input cubic_note ⟨(3 : Ordinal), cubic_note_repr⟩ hlarge t u e c hT htu he hc
  rw [cubic_note_repr] at h
  exact (Nat.le_add_right _ _).trans_lt h

end LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof
