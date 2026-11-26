module
public import LogicLineages.PermittedControl.AffineCollapseTopologicalLowTargets
import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalLow
open AffineCollapsePairListLow (Pair)
open AffineCollapseTopologicalExtension (Valuation AgreesOutside born exactTopologicalExtension)

theorem exactTestedExternalExtension : ExactTestedExternalExtension := by
  intro f B sel known pairs top external prior testRows test positive
  have result := exactTopologicalExtension f B sel known pairs top external
  constructor
  · rintro ⟨final,run,pr,vals,actual,holds⟩
    obtain ⟨graphs,agree⟩ := (result final).mp run
    exact ⟨final,graphs,agree,pr,vals,actual,holds⟩
  · rintro ⟨final,graphs,agree,pr,vals,actual,holds⟩
    exact ⟨final,(result final).mpr ⟨graphs,agree⟩,pr,vals,actual,holds⟩

theorem sameExternalUpdate (pairs : List Pair) (base shared : Valuation) (rank a : Nat)
    (agree : AgreesOutside pairs base shared) :
    AgreesOutside pairs (Function.update base rank a) (Function.update shared rank a) := by
  intro n untouched
  by_cases same : n = rank
  · subst n
    simp only [Function.update_self]
  · simp only [Function.update_of_ne same]
    exact agree n untouched

/-- Reset only the external coordinate in the pre-update shared
valuation. This changes neither the earlier named witnesses nor any
other exterior coordinate. -/
theorem factorExternalUpdate (pairs : List Pair) (base final : Valuation) (rank a : Nat)
    (exterior : rank ∉ born pairs) (agree : AgreesOutside pairs (Function.update base rank a) final) :
    ∃ shared : Valuation, AgreesOutside pairs base shared ∧
      Function.update shared rank a = final := by
  let shared := Function.update final rank (base rank)
  refine ⟨shared,?_,?_⟩
  · intro n untouched
    by_cases same : n = rank
    · subst n
      exact Function.update_self _ _ _
    · change Function.update final rank (base rank) n = base n
      rw [Function.update_of_ne same]
      exact (agree n untouched).trans (Function.update_of_ne same _ _)
  · funext n
    by_cases same : n = rank
    · subst n
      rw [Function.update_self]
      exact ((agree rank exterior).trans (Function.update_self _ _ _)).symm
    · change Function.update (Function.update final rank (base rank)) rank a n = final n
      simp only [Function.update_of_ne same]

end LogicLineages.PermittedControl.AffineCollapseTopologicalLow
