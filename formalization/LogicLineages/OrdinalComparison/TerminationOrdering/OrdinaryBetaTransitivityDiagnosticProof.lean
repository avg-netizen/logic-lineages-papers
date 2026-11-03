module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticStepsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticObstructionsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetFunctionalInversionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison
open OrdinaryBetaTransitivityDiagnostic OrdinaryBetaTransitivityDiagnosticObstructionsProof
open OriginalBudgetFunctionalInversionProof

def Blocks (n : Nat) : Prop :=
  (¬OriginalDerivationBudget.Weak Nat arity above n [] ⟨.ground,q⟩ ⟨.ground,u⟩) ∧
  (¬OriginalDerivationBudget.Weak Nat arity above n [] ⟨.ground,s⟩ ⟨.ground,u⟩) ∧
  (¬OriginalDerivationBudget.Weak Nat arity above n [] ⟨.ground,markedS⟩ ⟨.ground,u⟩) ∧
  (¬OriginalDerivationBudget.Weak Nat arity above n [] ⟨.ground,p⟩ ⟨.ground,u⟩)

theorem allBudgetsBlocked (n : Nat) : Blocks n := by
  induction n with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> cases h
  | succ n ih =>
    refine ⟨?_,?_,?_,?_⟩
    · intro hq
      rcases markedGroundFrame above n _ _ hq (.application .ground .ground) applicationBase 3 (.cons h (.cons h .nil)) rfl rfl with hp | ⟨he,hm⟩ | ⟨sigma,selected,types,suffix,result,hmem,ha,hw⟩ | hup
      · cases hp
      · cases he
      · change (⟨sigma,selected⟩ : Packed Nat arity [])∈[⟨.arrow .ground .ground,.lam (embed bodyOriginal)⟩,⟨.ground,k⟩] at hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with he | he
        · cases he
          cases types with
          | nil => cases suffix
          | cons rho rest =>
            obtain ⟨hdom,hcod⟩ := Ty.arrow.inj suffix
            cases hdom
            cases rest with
            | nil =>
              have hr : s=result := Option.some.inj ha
              subst result
              exact ih.2.1 hw
            | cons rho rest => cases hcod
        · cases he
          cases types with
          | nil =>
            have hr : k=result := Option.some.inj ((SourceSpecialApplicationProof.emptySpecialApplication Nat arity [] .ground k).symm.trans ha)
            subst result
            exact kNotU (OriginalDerivationBudgetErasureProof.weakSound hw)
          | cons rho rest => cases suffix
      · exact ih.1 hup
    · intro hs
      rcases ordinaryFrame above n _ _ hs (.ranked 3) (.ranked 3) (.cons q (.cons z .nil)) (.cons h (.cons h .nil)) rfl rfl with ⟨he,matched,hp,hm⟩ | hmark | hup
      · exact noWeakMatching matched hp hm
      · exact ih.2.2.1 hmark
      · exact ih.2.1 hup
    · intro hs
      rcases markedGroundFrame above n _ _ hs (.ranked 3) (.cons q (.cons z .nil)) 3 (.cons h (.cons h .nil)) rfl rfl with hp | ⟨he,hm⟩ | ⟨sigma,selected,types,suffix,result,hmem,ha,hw⟩ | hup
      · change 3<3 at hp
        exact Nat.lt_irrefl 3 hp
      · exact noStrictMultiset hm
      · change (⟨sigma,selected⟩ : Packed Nat arity [])∈[⟨.ground,q⟩,⟨.ground,z⟩] at hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with he | he
        · cases he
          cases types with
          | nil =>
            have hr : q=result := Option.some.inj ((SourceSpecialApplicationProof.emptySpecialApplication Nat arity [] .ground q).symm.trans ha)
            subst result
            exact ih.1 hw
          | cons rho rest => cases suffix
        · cases he
          cases types with
          | nil =>
            have hr : z=result := Option.some.inj ((SourceSpecialApplicationProof.emptySpecialApplication Nat arity [] .ground z).symm.trans ha)
            subst result
            exact zeroNotU (OriginalDerivationBudgetErasureProof.weakSound hw)
          | cons rho rest => cases suffix
      · exact ih.2.2.1 hup
    · intro hp
      rcases ordinaryFrame above n _ _ hp (.application .ground .ground) (.ranked 3) applicationBase (.cons h (.cons h .nil)) rfl rfl with ⟨he,matched,hperm,hm⟩ | hmark | hup
      · cases he
      · exact ih.1 hmark
      · exact ih.2.2.2 hup

theorem ordinaryFailure : OrdinaryBetaTransitivityDiagnosticTargets.ActualOrdinaryFailure := by
  intro hp
  obtain ⟨n,hn⟩ := OriginalDerivationBudgetCompletenessProof.weakComplete above hp
  exact (allBudgetsBlocked n).2.2.2 hn

theorem weakTransitivityRefutation : OrdinaryBetaTransitivityDiagnosticTargets.ActualWeakTransitivityRefutation := by
  intro H
  have habove : Transitive above := fun _ _ _ hab hbc => Nat.lt_trans hbc hab
  have steps := OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps
  exact ordinaryFailure (H Nat arity above habove [] .ground pOriginal tOriginal uOriginal steps.1
    (RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _ steps.2))

theorem weakStrictRefutation : OrdinaryBetaTransitivityDiagnosticTargets.ActualWeakStrictRefutation := by
  intro H
  have habove : Transitive above := fun _ _ _ hab hbc => Nat.lt_trans hbc hab
  have steps := OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps
  exact ordinaryFailure (RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _
    (H Nat arity above habove [] .ground pOriginal tOriginal uOriginal steps.1 steps.2))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticProof
