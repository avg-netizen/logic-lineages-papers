import LogicLineages.PersistentMarking.NumberedWindowConstructorContextCasesProof
import LogicLineages.PersistentMarking.NumberedWindowConstructorFAbsCaseProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorComputabilityProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass NumberedWindowRules
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorOrderTargets
open NumberedWindowConstructorComputabilityTargets NumberedWindowConstructorRepresentationProof
open NumberedWindowConstructorContextCasesProof

theorem raw : AllConstructorRawCases := by
  intro S K Γ hk o b e sb se hw mb me ih r reduction hr
  cases o with
  | ordinary f bs =>
    change RawStep S K (.ordinary f bs) r at reduction
    cases reduction with
    | mark =>
      rename_i k
      have hf := (ownerParts (.ordinary f bs) hw).1
      exact ih (.numbered f f.result k bs .nil) b e sb se
        (Or.inr ⟨sameHead hf,Or.inr ⟨List.Perm.refl _,Or.inl True.intro⟩⟩) hr mb me
    | bottom => exact bottom hr
    | ordinaryBase step =>
      exact base (.ordinary f bs) (.ordinary f _) sb se mb me ih hr rfl rfl step
  | numbered f τ k bs es =>
    change RawStep S K (.numbered f τ k bs es) r at reduction
    cases reduction with
    | lower =>
      rename_i k
      have hf := (ownerParts (.numbered f τ (k+1) bs es) hw).1
      exact ih (.numbered f τ k bs es) b e sb se
        (Or.inr ⟨sameHead hf,Or.inr ⟨List.Perm.refl _,Or.inl (Nat.lt_succ_self k)⟩⟩) hr mb me
    | select get typed applied =>
      exact NumberedWindowConstructorSelectionCasesProof.select hk b e sb se hw mb me ih get typed applied
    | copy prec head =>
      exact NumberedWindowConstructorSelectionCasesProof.copy hk b e sb se hw mb me ih prec head
    | stat eq _ replaced => exact stat sb mb ih hr eq replaced
    | fabs => exact NumberedWindowConstructorFAbsCaseProof.fabs hk b e sb se hw mb me ih hr
    | bottom => exact bottom hr
    | numberedBase step =>
      exact base (.numbered f τ k bs es) (.numbered f τ k _ es) sb se mb me ih hr rfl rfl step
    | numberedExtra step => exact extras sb se mb me ih hr step

theorem owners : AllConstructorsComputable :=
  fun S K Γ hk => NumberedWindowConstructorInductionProof.fromRaw S K Γ hk (raw S K Γ hk)

end LogicLineages.PersistentMarking.NumberedWindowConstructorComputabilityProof
