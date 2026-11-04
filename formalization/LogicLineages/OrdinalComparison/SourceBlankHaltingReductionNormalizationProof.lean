module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof

/-- Normalization is a fixed primitive-recursive construction on program codes. -/
theorem normalize_primitive : Primrec normalize :=
  Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const Nat.Partrec.Code.zero)
    (Nat.Partrec.Code.primrec₂_comp.comp Primrec.id
      (Primrec.const Nat.Partrec.Code.zero))

/-- Decoding, normalizing, and re-encoding preserves primitive recursiveness. -/
theorem normalized_index_primitive : Primrec normalizedIndex :=
  Primrec.encode.comp (normalize_primitive.comp (Primrec.ofNat Nat.Partrec.Code))

/-- The normalized program ignores its input and returns zero exactly when the
original program terminates on zero. This concerns partial evaluation, not time. -/
theorem normalize_eval (c : Nat.Partrec.Code) (x : Nat) :
    (normalize c).eval x = (fun _ : Nat => 0) <$> c.eval 0 := by
  change ((Part.some 0).bind c.eval).bind (fun _ => Part.some 0) =
    Part.map (fun _ : Nat => 0) (c.eval 0)
  rw [Part.bind_some, Part.bind_some_eq_map]

theorem exactNormalization : Targets.ExactNormalization :=
  ⟨normalize_primitive, normalized_index_primitive, normalize_eval⟩

end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
