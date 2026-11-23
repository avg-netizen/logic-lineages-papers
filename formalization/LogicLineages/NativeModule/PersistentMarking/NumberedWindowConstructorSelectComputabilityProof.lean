module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorSelectComputabilityTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalComputabilityChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorSelectComputabilityProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowConstructorArgumentAddresses
open NumberedWindowExternalApplication NumberedWindowExternalComputability
open NumberedWindowConstructorSelectComputabilityTargets
open NumberedWindowApplicationTargets (ArgsWindow)
open NumberedWindowApplicationDomainProof (appEq annotation)
open NumberedWindowExternalComputabilityChecks (exact_ArrowAtEveryTypedArgument)

private theorem computedAt {S K Γ hk q τ} (hw : InWindow S K (finiteC Γ) τ q)
    (h : ComputableArgument S K Γ hk q) : ComputableClass S K Γ hk τ (classOf ⟨q, hw⟩) := by
  unfold ComputableArgument at h
  rw [annotation hw.1] at h
  obtain ⟨_, hc⟩ := h
  exact hc

theorem tuple : TypedAuxiliaryApplicationsComputable := by
  intro S K Γ hk ds τ q args out hq hc hArgs hComputable hCall
  induction hArgs generalizing q with
  | nil =>
    have hEq : q = out := Option.some.inj hCall
    subst out
    exact ⟨hq, hc⟩
  | cons ha _ ih =>
    let step := appCarrier hk ⟨q, hq⟩ ⟨_, ha⟩
    have hArgument := computedAt ha (hComputable _ List.mem_cons_self)
    have hApplied : ComputableClass S K Γ hk _ (classOf step) :=
      (exact_ArrowAtEveryTypedArgument S K Γ _ _ hk (classOf ⟨q, hq⟩)).mp hc _ hArgument
    have hTailCall := (appEq hq.1 ha.1 _).symm.trans hCall
    exact ih step.val step.property hApplied
      (fun u hu => hComputable u (List.mem_cons_of_mem _ hu)) hTailCall

private theorem getMember (xs : NArgs) (i : Nat) (q : NTerm) (h : xs.get i = some q) : q ∈ xs.toList := by
  cases xs with
  | nil => cases h
  | cons a rest =>
    cases i with
    | zero =>
      have e : a = q := Option.some.inj h
      subst q
      exact List.mem_cons_self
    | succ i => exact List.mem_cons_of_mem _ (getMember rest i q h)
termination_by i

private theorem copiesWindow {S K Γ hk} (f : Head) (k : Nat) (bs es : NArgs) (ds : List Ty)
    (h : ∀ q ∈ (ownerCopies f k bs es ds).toList, ComputableArgument S K Γ hk q) :
    ArgsWindow S K (finiteC Γ) ds (ownerCopies f k bs es ds) := by
  induction ds with
  | nil => exact .nil
  | cons σ tail ih =>
    obtain ⟨hSelf, _⟩ := h (.numbered f σ k bs es) List.mem_cons_self
    exact .cons hSelf (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem select : SelectFromComputableCopies := by
  intro S K Γ hk f τ k bs es i selected ds out hBase hExtra hGet hType hCopies hCall
  have hSelected : ComputableArgument S K Γ hk selected := hGet.elim
    (fun h => hBase selected (getMember bs i selected h))
    (fun h => hExtra selected (getMember es i selected h))
  unfold ComputableArgument at hSelected
  rw [hType] at hSelected
  obtain ⟨hw, hc⟩ := hSelected
  exact tuple S K Γ hk ds τ selected _ out hw hc (copiesWindow f k bs es ds hCopies) hCopies hCall

end LogicLineages.PersistentMarking.NumberedWindowConstructorSelectComputabilityProof
