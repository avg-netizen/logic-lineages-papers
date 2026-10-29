module
public import LogicLineages.Ultrafilters.NearZeroCompactProof
public import Mathlib.Topology.Algebra.Semigroup
@[expose] public section
namespace LogicLineages.Ultrafilters

theorem admissible_exists : Targets.AdmissibleExistence := by
  obtain ⟨hmem, hassoc, hcont⟩ := convolution_laws
  obtain ⟨hne, hclosed, hcompact, hclosedAdd⟩ := nearZero_compactSemigroup
  letI : AddSemigroup (Ultrafilter ℝ) :=
    { add := convolution, add_assoc := hassoc }
  obtain ⟨p, hp, hi⟩ := exists_idempotent_in_compact_add_subsemigroup
    hcont {p : Ultrafilter ℝ | NearZero p} hne hcompact (fun p hp q hq => hclosedAdd p q hp hq)
  refine ⟨p, ?_, hp⟩
  intro s
  change convolution p p = p at hi
  rw [← hmem, hi]

end LogicLineages.Ultrafilters
