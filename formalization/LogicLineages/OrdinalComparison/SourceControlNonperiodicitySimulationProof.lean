module
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof

theorem program_primitive : Primrec program := Primrec.ofNat Nat.Partrec.Code

theorem bounded_primitive : Primrec boundedH := by
  have he : Primrec (fun p : Nat × Nat => Nat.Partrec.Code.evaln p.2 (program p.1) 0) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair (program_primitive.comp Primrec.fst)).pair (Primrec.const 0))
  apply (Primrec.not.comp ((Primrec.eq.comp he (Primrec.const none)).decide)).of_eq
  intro p
  unfold boundedH
  cases Nat.Partrec.Code.evaln p.2 (program p.1) 0 <;> rfl

theorem program_roundtrip (c : Nat.Partrec.Code) : program (Encodable.encode c) = c :=
  Denumerable.ofNat_encode c

theorem bounded_sound (e t : Nat) (h : boundedH (e,t) = true) :
    (Nat.Partrec.Code.eval (program e) 0).Dom := by
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h
  exact Part.dom_iff_mem.mpr ⟨x,Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hx)⟩

theorem halting_iff (e : Nat) : (Nat.Partrec.Code.eval (program e) 0).Dom ↔
    ∃ t : Nat, boundedH (e,t) = true := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    exact ⟨t,Option.isSome_iff_exists.mpr ⟨x,Option.mem_def.mp ht⟩⟩
  · rintro ⟨t,ht⟩
    exact bounded_sound e t ht

theorem bounded_mono (e t u : Nat) (htu : t ≤ u) (h : boundedH (e,t) = true) :
    boundedH (e,u) = true := by
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨x,Option.mem_def.mp
    (Nat.Partrec.Code.evaln_mono htu (Option.mem_def.mpr hx))⟩

theorem effectiveBoundedSimulation : Targets.EffectiveBoundedSimulation :=
  ⟨program_primitive,bounded_primitive,program_roundtrip,halting_iff,bounded_mono⟩
end LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof
