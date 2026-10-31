module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassProof
public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixProof
open PredictionTapeObservation PredictionTapeRuntime PredictionTapeRuntimeClass
open PredictionTapeMembershipMatrix PredictionTapeMembershipMatrixTargets

theorem exactFiniteCertificate : ExactFiniteCertificate := by
  intro code cutoff fuel
  simp only [finiteCheck, List.all_eq_true, List.mem_range]
  constructor
  · intro h xs hx
    exact h xs.length (by omega) xs ((PredictionCommonFuelProof.booleanHistoriesExact _ _).2 rfl)
  · intro h n hn xs hx
    have he := (PredictionCommonFuelProof.booleanHistoriesExact n xs).1 hx
    exact h xs (by omega)

private theorem successful_iff (code : Nat) (he : TotalBinary code) (budget : Nat) (xs : List Bool) :
    (boundedMove code budget xs).isSome = true ↔ Successful code xs (budget - 1) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨v, hv, _⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨d, hd, _⟩ := Option.map_eq_some_iff.mp hv
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    have ho : observe code budget xs = some (d.2.1 % PredictionFiniteAlphabet.width (PredictionFiniteAlphabet.decodeTable code)) :=
      congrArg (Option.map (fun z : PredictionFiniteAlphabet.Raw =>
        z.2.1 % PredictionFiniteAlphabet.width (PredictionFiniteAlphabet.decodeTable code))) hd
    have hr := (PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ _).2
      (PredictionTapeObservationProof.observationUniqueOnTotal code he budget xs _ ho)
    have hb : boundedMove code budget xs = some (policy code he xs) := by
      unfold boundedMove
      rw [ho]
      exact hr
    exact congrArg Option.isSome hb

theorem totalFiniteCertificate : TotalFiniteCertificate := by
  classical
  intro code he cutoff
  choose t ht using totalBinaryWorstExists code he
  let F := (Finset.range (cutoff + 1)).sup (fun n => t n + 1)
  refine ⟨F, (exactFiniteCertificate code cutoff F).2 ?_⟩
  intro xs hx
  have hF : t xs.length + 1 ≤ F := Finset.le_sup (s := Finset.range (cutoff + 1)) (f := fun n => t n + 1) (by simp only [Finset.mem_range]; omega)
  apply (successful_iff code he F xs).2
  exact ((worstTimeThreshold code xs.length (t xs.length)).1 (ht xs.length) (F - 1)).2
    (by omega) xs rfl

private theorem value_mem (bound : Nat.Partrec.Code) (hf : PredictionCanonicalList.TotalNat bound) (n : Nat) :
    PredictionMaximum.evalValue bound n ∈ Nat.Partrec.Code.eval bound n := by
  have hd : (Nat.Partrec.Code.eval bound n).Dom := (hf n).choose_spec.1
  simp only [PredictionMaximum.evalValue, dif_pos hd]
  exact ⟨hd, rfl⟩

private theorem guard_success (code : Nat) (bound : Nat.Partrec.Code) (cutoff : Nat)
    (hf : PredictionCanonicalList.TotalNat bound)
    (hguard : ∀ xs stage, guardedCheck code bound cutoff xs stage = true)
    (xs : List Bool) (hcut : cutoff < xs.length) :
    (boundedMove code (PredictionMaximum.evalValue bound xs.length) xs).isSome = true := by
  obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp (value_mem bound hf xs.length)
  have hg := hguard xs s
  simpa only [guardedCheck, if_pos hcut, Option.mem_def.mp hs] using hg

theorem sourceMembership : SourceMembership := by
  intro code bound hf
  constructor
  · rintro ⟨he, htime⟩
    obtain ⟨N, hN⟩ := (PredictionTapeRuntimeClassProof.exactAvailabilityCalibration code he _).2 htime
    obtain ⟨F, hF⟩ := totalFiniteCertificate code he N
    refine ⟨Nat.pair N F, ?_⟩
    intro query
    simp only [membershipMatrix, Nat.unpair_pair, hF, Bool.true_and]
    let xs := ((Encodable.decode (α := List Bool) query.unpair.1).getD [])
    change guardedCheck code bound N xs query.unpair.2 = true
    unfold guardedCheck
    split_ifs with hlen
    · cases hs : Nat.Partrec.Code.evaln query.unpair.2 bound xs.length with
      | none => rfl
      | some v =>
        have hv : v = PredictionMaximum.evalValue bound xs.length :=
          Part.mem_unique (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hs)) (value_mem bound hf xs.length)
        rw [hv]
        exact congrArg Option.isSome (hN xs.length (by omega) xs rfl)
    · rfl
  · rintro ⟨w, hw⟩
    have hfinite : finiteCheck code w.unpair.1 w.unpair.2 = true := by
      have h := hw 0
      simp only [membershipMatrix, Bool.and_eq_true] at h
      exact h.1
    have hg : ∀ xs stage, guardedCheck code bound w.unpair.1 xs stage = true := by
      intro xs stage
      have h := hw (Nat.pair (Encodable.encode xs) stage)
      simp only [membershipMatrix, Bool.and_eq_true] at h
      simpa only [Nat.unpair_pair, Encodable.encodek, Option.getD_some] using h.2
    have he : TotalBinary code := by
      intro xs
      by_cases hlen : xs.length ≤ w.unpair.1
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((exactFiniteCertificate _ _ _).1 hfinite xs hlen)
        exact ⟨b, (PredictionTapeObservationProof.exactBinarySemantics _ _ _).2 ⟨w.unpair.2, hb⟩⟩
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (guard_success code bound w.unpair.1 hf hg xs (by omega))
        exact ⟨b, (PredictionTapeObservationProof.exactBinarySemantics _ _ _).2
          ⟨PredictionMaximum.evalValue bound xs.length, hb⟩⟩
    refine ⟨he, w.unpair.1 + 1, ?_⟩
    intro n hn
    apply (strictBudgetCalibration code n (PredictionMaximum.evalValue bound n)).2
    intro xs hx
    have hs := guard_success code bound w.unpair.1 hf hg xs (by omega)
    rw [hx] at hs
    exact (successful_iff code he (PredictionMaximum.evalValue bound n) xs).1 hs

private theorem pr_all {α β : Type} [Primcodable α] [Primcodable β]
    (l : α → List β) (p : α → β → Bool) (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec (fun a => (l a).all (p a)) := by
  have h := Primrec.list_foldr hl (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)))
  apply h.of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => simp [List.all_cons, ih]

private theorem pr_move : Primrec (fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2) :=
  PredictionTapeObservationProof.effectiveObservation.2

private abbrev FC := Nat × Nat × Nat
private abbrev GC := Nat × Nat.Partrec.Code × Nat × List Bool × Nat
private abbrev MC := Nat × Nat.Partrec.Code × Nat × Nat

private theorem pr_one : Primrec (fun z : (FC × Nat) × List Bool =>
    (boundedMove z.1.1.1 z.1.1.2.2 z.2).isSome) := by
  have ha : Primrec (fun z : (FC × Nat) × List Bool => (z.1.1.1, z.1.1.2.2, z.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd)
  exact Primrec.option_isSome.comp (Primrec.comp
    (f := fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2)
    (g := fun z : (FC × Nat) × List Bool => (z.1.1.1, z.1.1.2.2, z.2)) pr_move ha)

private theorem pr_finite : Primrec (fun z : FC => finiteCheck z.1 z.2.1 z.2.2) := by
  have hinner : Primrec (fun z : FC × Nat => (PredictionCommonFuel.booleanHistories z.2).all
      (fun xs => (boundedMove z.1.1 z.1.2.2 xs).isSome)) :=
    pr_all _ _ (PredictionCommonFuelProof.booleanHistoriesPrimrec.comp Primrec.snd) pr_one.to₂
  exact pr_all _ _ (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) hinner.to₂

private theorem pr_guard : Primrec (fun z : GC => guardedCheck z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  have hc : Primrec (fun z : GC => z.1) := Primrec.fst
  have hf : Primrec (fun z : GC => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : GC => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec (fun z : GC => z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun z : GC => z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hv : Primrec (fun z : GC => Nat.Partrec.Code.evaln z.2.2.2.2 z.2.1 z.2.2.2.1.length) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hs.pair hf).pair (Primrec.list_length.comp hx))
  have hb : Primrec (fun z : GC × Nat => (boundedMove z.1.1 z.2 z.1.2.2.2.1).isSome) :=
    Primrec.option_isSome.comp (Primrec.comp
      (f := fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2)
      (g := fun z : GC × Nat => (z.1.1, z.2, z.1.2.2.2.1)) pr_move
      ((hc.comp Primrec.fst).pair (Primrec.snd.pair (hx.comp Primrec.fst))))
  apply (Primrec.ite (Primrec.nat_lt.comp hn (Primrec.list_length.comp hx))
    (Primrec.option_casesOn hv (Primrec.const true) hb.to₂) (Primrec.const true)).of_eq
  intro z
  unfold guardedCheck
  split_ifs <;> cases Nat.Partrec.Code.evaln z.2.2.2.2 z.2.1 z.2.2.2.1.length <;> rfl

theorem effectiveMembershipMatrix : EffectiveMembershipMatrix := by
  have hc : Primrec (fun z : MC => z.1) := Primrec.fst
  have hf : Primrec (fun z : MC => z.2.1) := Primrec.fst.comp Primrec.snd
  have hw : Primrec (fun z : MC => z.2.2.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hq : Primrec (fun z : MC => z.2.2.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec (fun z : MC => ((Encodable.decode (α := List Bool) z.2.2.2.unpair.1).getD [])) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hq)) (Primrec.const [])
  exact Primrec.and.comp
    (Primrec.comp (f := fun z : FC => finiteCheck z.1 z.2.1 z.2.2)
      (g := fun z : MC => (z.1, z.2.2.1.unpair.1, z.2.2.1.unpair.2)) pr_finite
      (hc.pair ((Primrec.fst.comp hw).pair (Primrec.snd.comp hw))))
    (Primrec.comp (f := fun z : GC => guardedCheck z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
      (g := fun z : MC => (z.1, z.2.1, z.2.2.1.unpair.1,
        ((Encodable.decode (α := List Bool) z.2.2.2.unpair.1).getD []), z.2.2.2.unpair.2)) pr_guard
      (hc.pair (hf.pair ((Primrec.fst.comp hw).pair (hx.pair (Primrec.snd.comp hq))))))

end LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixProof
