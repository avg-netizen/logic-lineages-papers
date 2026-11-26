module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryClassListTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFiniteSaturationReachProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryCoverSyntax NumberedWindowPrimarySequence
open NumberedWindowLiteralEquality NumberedWindowPrimaryExchangeBits
open NumberedWindowFiniteSaturation NumberedWindowPrimaryClassList
open NumberedWindowPrimaryClassListTargets

private theorem literalSame : EqualityTest termEq :=
  NumberedWindowTypingBitsChecks.exact_LiteralTermEquality

private theorem graphSound {S K C τ seed R} (hSeed : InWindow S K C τ seed)
    (p : GraphReach (cover S K seed) (windowExchangeBit S K C τ) seed R) :
    Primary S K C τ seed R := by
  induction p with
  | start _ => exact .refl hSeed.1
  | @next W V _ _ hbit ih =>
    have he := (NumberedWindowPrimaryExchangeChecks.exact_WindowExchangeReflection S K C τ W V).mp hbit
    exact .trans ih (NumberedWindowPrimaryExchangeChecks.exact_WindowExchangeSound S K C τ W V he)

private theorem graphComplete {S K C τ seed Q R} (hk : DecisionSourceUniverse.Closed K)
    (hSeed : InWindow S K C τ seed) (p : AdmittedExchangeTrace S K C τ Q R) :
    Primary S K C τ seed Q →
    GraphReach (cover S K seed) (windowExchangeBit S K C τ) seed Q →
    GraphReach (cover S K seed) (windowExchangeBit S K C τ) seed R := by
  induction p with
  | refl _ => intro _ h; exact h
  | next he _ ih =>
    intro hp hReach
    have hs := NumberedWindowPrimaryExchangeChecks.exact_WindowExchangeSound S K C τ _ _ he
    have hp' := Primary.trans hp hs
    have hV := NumberedWindowPrimaryCoverChecks.exact_FinitePrimaryClassCover
      S K C τ seed _ hk hSeed hp'
    have hBit := (NumberedWindowPrimaryExchangeChecks.exact_WindowExchangeReflection S K C τ _ _).mpr he
    exact ih hp' (.next hReach hV hBit)

theorem abstractList : AbstractExactPrimaryClassList := by
  intro S K C τ Q R hk hQ
  unfold classList
  rw [NumberedWindowFiniteSaturationReachProof.reach
    (cover S K Q) termEq (windowExchangeBit S K C τ) Q R literalSame]
  constructor
  · intro h
    exact graphSound hQ h
  · intro h
    obtain ⟨p⟩ := (NumberedWindowPrimarySequenceChecks.exact_AdmittedPrimarySequences
      S K C τ Q R hk hQ).mp h
    have hRefl : Primary S K C τ Q Q := .refl hQ.1
    have hCover := NumberedWindowPrimaryCoverChecks.exact_FinitePrimaryClassCover
      S K C τ Q Q hk hQ hRefl
    exact graphComplete hk hQ p hRefl (.start hCover)

theorem finiteList : ExactFinitePrimaryClassList := by
  intro S K Γ τ Q R hk hQ
  unfold finiteClassList
  rw [NumberedWindowFiniteBinderProof.lookup Γ]
  exact abstractList S K _ τ Q R hk hQ

private theorem anyLiteral (R : NTerm) (xs : List NTerm) :
    xs.any (termEq R) = true ↔ R ∈ xs := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r,hr,he⟩
    exact ((literalSame R r).mp he).symm ▸ hr
  · intro h
    exact ⟨R,h,(literalSame R R).mpr rfl⟩

theorem decision : ExactFinitePrimaryDecision := by
  intro S K Γ τ Q R hk hQ
  exact (anyLiteral R (finiteClassList S K Γ τ Q)).trans (finiteList S K Γ τ Q R hk hQ)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListProof
