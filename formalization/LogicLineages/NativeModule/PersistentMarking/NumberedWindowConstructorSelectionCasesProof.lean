module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorComputabilityTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorSelectComputabilityChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorArgumentAddressChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationHeadProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorSelectionCasesProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowConstructorArgumentAddresses
open NumberedWindowConstructorOrderTargets NumberedWindowConstructorComputabilityTargets
open NumberedWindowConstructorArgumentAddressChecks NumberedWindowConstructorSelectComputabilityChecks
open NumberedWindowExternalComputability
open NumberedWindowApplicationDomainProof (annotation rootInWindow arrowLeft arrowRight subtypeSelf)
open Spine (ArrowPrefix)

theorem literalArgument {S K Γ hk τ q} (hw : InWindow S K (finiteC Γ) τ q)
    (h : ComputableClass S K Γ hk τ (classOf ⟨q, hw⟩)) : ComputableArgument S K Γ hk q := by
  unfold ComputableArgument
  rw [annotation hw.1]
  exact ⟨hw, h⟩

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

private theorem arrowDomains {K : List Ty} (hk : DecisionSourceUniverse.Closed K)
    (ds : List Ty) (τ : Ty) (h : ArrowPrefix ds τ ∈ K) : ∀ t ∈ ds, t ∈ K := by
  induction ds with
  | nil => intro t ht; exact (List.not_mem_nil ht).elim
  | cons σ ds ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact arrowLeft hk h _ (subtypeSelf _)
    · exact ih (arrowRight hk h _ (subtypeSelf _)) t ht

private theorem copies {S K Γ f τ k bs es} (hk : DecisionSourceUniverse.Closed K)
    (bc ec : List Nat) (hbc : Slots S K Γ bs bc) (hec : Slots S K Γ es ec)
    (hw : InWindow S K (finiteC Γ) τ (.numbered f τ (k + 1) bs es))
    (hBase : Members S K Γ hk bs) (hExtra : Members S K Γ hk es)
    (earlier : Hypothesis S K Γ hk ((Owner.numbered f τ (k + 1) bs es).measure bc ec))
    (ds : List Ty) (hDomains : ∀ σ ∈ ds, σ ∈ K) : Members S K Γ hk (ownerCopies f k bs es ds) := by
  obtain ⟨hBaseTyped, hExtraTyped, hHead, hBaseGuard, hExtraGuard⟩ := NumberedWindowNumberedDomainProof.parts hw
  obtain ⟨rank, hRank⟩ := hHead.1
  induction ds with
  | nil => intro q hq; cases hq
  | cons σ tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hTail
    · have hWindow : InWindow S K (finiteC Γ) σ (.numbered f σ k bs es) :=
        NumberedWindowNumberedDomainProof.numbered hBaseTyped hExtraTyped hHead
          (hk σ (hDomains σ List.mem_cons_self)) hBaseGuard hExtraGuard
      have hEarlier : Earlier S K ((Owner.numbered f σ k bs es).measure bc ec)
          ((Owner.numbered f τ (k + 1) bs es).measure bc ec) :=
        .inr ⟨⟨rank, hRank, hRank⟩, .inr ⟨.rfl, .inl (Nat.lt_succ_self k)⟩⟩
      exact earlier (.numbered f σ k bs es) bc ec hbc hec hEarlier hWindow hBase hExtra
    · exact ih (fun t ht => hDomains t (List.mem_cons_of_mem _ ht)) q hTail

theorem select {S K Γ f τ k bs es i q ds out} (hk : DecisionSourceUniverse.Closed K)
    (bc ec : List Nat) (hbc : Slots S K Γ bs bc) (hec : Slots S K Γ es ec)
    (hw : InWindow S K (finiteC Γ) τ (.numbered f τ (k + 1) bs es))
    (hBase : Members S K Γ hk bs) (hExtra : Members S K Γ hk es)
    (earlier : Hypothesis S K Γ hk ((Owner.numbered f τ (k + 1) bs es).measure bc ec))
    (hGet : bs.get i = some q ∨ es.get i = some q) (hType : q.type = ArrowPrefix ds τ)
    (hCall : applications q (ownerCopies f k bs es ds) = some out) : ComputableArgument S K Γ hk out := by
  obtain ⟨hSelected, _⟩ := hGet.elim
    (fun h => hBase q (getMember bs i q h)) (fun h => hExtra q (getMember es i q h))
  have hArrow : ArrowPrefix ds τ ∈ K := hType ▸ rootInWindow hSelected
  have hCopies := copies hk bc ec hbc hec hw hBase hExtra earlier ds (arrowDomains hk ds τ hArrow)
  obtain ⟨hResult, hComputable⟩ := exact_SelectFromComputableCopies S K Γ hk f τ k bs es i q ds out
    hBase hExtra hGet hType hCopies hCall
  exact literalArgument hResult hComputable

theorem copy {S K Γ f g k bs es} (hk : DecisionSourceUniverse.Closed K)
    (bc ec : List Nat) (hbc : Slots S K Γ bs bc) (hec : Slots S K Γ es ec)
    (hw : InWindow S K (finiteC Γ) g.result (.numbered f g.result (k + 1) bs es))
    (hBase : Members S K Γ hk bs) (hExtra : Members S K Γ hk es)
    (earlier : Hypothesis S K Γ hk ((Owner.numbered f g.result (k + 1) bs es).measure bc ec))
    (hPrec : Spine.Precedes S f g) (hTargetHead : HeadInWindow S K g) :
    ComputableArgument S K Γ hk (.ordinary g (ownerCopies f k bs es g.arguments)) := by
  have hDomains : ∀ σ ∈ g.arguments, σ ∈ K := by
    intro σ hσ
    exact hTargetHead.2 σ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ, hσ, subtypeSelf σ⟩))
  have hCopies := copies hk bc ec hbc hec hw hBase hExtra earlier g.arguments hDomains
  obtain ⟨targetCodes, hTargetCodes, _, _⟩ :=
    exact_ComputableArgumentsGiveMultiset S K Γ hk _ hCopies
  have hTarget := NumberedWindowPreservationHeadProof.copy hk hw hTargetHead
  exact earlier (.ordinary g (ownerCopies f k bs es g.arguments)) targetCodes [] hTargetCodes rfl
    (.inl hPrec) hTarget hCopies (by intro q hq; cases hq)

end LogicLineages.PersistentMarking.NumberedWindowConstructorSelectionCasesProof
