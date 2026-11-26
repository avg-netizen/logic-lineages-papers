module
public import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsHopProof
open NumberedWindowConcretePositiveEndpointsTargets
open NumberedWindowConcreteCheckers (step)
open NumberedWindowPositivePathAlgorithm (advance hopView)
open NumberedWindowScalarAlgorithm (admitted least)

theorem hopReport : ExactConcretePositiveHopReport := by
  intro entries s ctx ty source code target ok
  cases seen : hopView code with
  | none => simp [advance,seen] at ok
  | some row =>
    rcases row with ⟨reported,q,w,r⟩
    have selected :
        (if step entries s ctx ty q w r && (least s ctx ty q == some source) &&
            (least s ctx ty r == some reported) then some reported else none) = some target := by
      simpa only [advance,Option.bind_eq_bind,Option.bind_some,seen] using ok
    by_cases guards : (step entries s ctx ty q w r && (least s ctx ty q == some source) &&
        (least s ctx ty r == some reported)) = true
    · rw [if_pos guards] at selected
      have same := Option.some.inj selected
      simp only [Bool.and_eq_true,beq_iff_eq,and_assoc] at guards
      have rawGuards :
          NumberedWindowRawContextAlgorithm.raw (NumberedWindowConcreteCheckers.root entries s)
            q w r = true ∧ admitted s ctx ty q = true ∧ admitted s ctx ty r = true := by
        simpa only [step,NumberedWindowRawContextAlgorithm.windowStep,Bool.and_eq_true,and_assoc]
          using guards.1
      exact ⟨q,w,r,by rw [same],guards.1,rawGuards.2.1,rawGuards.2.2,
        guards.2.1,same ▸ guards.2.2⟩
    · rw [if_neg guards] at selected
      cases selected

end LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsHopProof
