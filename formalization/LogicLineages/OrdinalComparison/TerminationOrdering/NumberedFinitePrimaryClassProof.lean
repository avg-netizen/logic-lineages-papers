module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedPrimaryExchange NumberedExchangeNeighborhood NumberedFinitePrimaryClass

local instance {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} : DecidableEq (Packed Symbol arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

theorem memStep {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) (A : Finset (Packed Symbol arity Gamma)) (r : Packed Symbol arity Gamma) :
    r∈reachStep symbols S q A ↔ r∈A ∨ r∈vertices symbols S q ∧ ∃ a∈A,exchangeTest symbols S a r=true := by
  simp [reachStep]

theorem subsetStep {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) (A : Finset (Packed Symbol arity Gamma)) :
    A ⊆ reachStep symbols S q A := fun r hr => (memStep symbols S q A r).mpr (Or.inl hr)

theorem reachableBound : NumberedFinitePrimaryClassTargets.ActualReachableBound := by
  intro Symbol inst arity symbols S Gamma q n
  induction n with
  | zero => intro r hr; simp only [reachable,Finset.mem_singleton] at hr; subst r; simp [vertices]
  | succ n ih =>
    intro r hr
    rcases (memStep symbols S q _ r).mp hr with hr | ⟨hr,_⟩
    · exact ih hr
    · exact hr

theorem initialMember {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) (n : Nat) : q∈reachable symbols S q n := by
  induction n with
  | zero => simp [reachable]
  | succ n ih => exact subsetStep symbols S q _ ih

theorem cardinalitySaturation : NumberedFinitePrimaryClassTargets.ActualCardinalitySaturation := by
  intro Symbol inst arity symbols S Gamma q
  have grow : ∀ n,reachable symbols S q n=reachable symbols S q (n+1) ∨ n<(reachable symbols S q (n+1)).card := by
    intro n
    induction n with
    | zero => exact Or.inr (Finset.card_pos.mpr ⟨q,initialMember symbols S q 1⟩)
    | succ n ih =>
      rcases ih with he | hcard
      · exact Or.inl (congrArg (reachStep symbols S q) he)
      · by_cases he : reachable symbols S q (n+1)=reachable symbols S q (n+1+1)
        · exact Or.inl he
        · right
          have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subsetStep symbols S q _,he⟩)
          change (reachable symbols S q (n+1)).card<(reachable symbols S q (n+1+1)).card at hlt
          omega
  rcases grow (vertices symbols S q).card with he | hcard
  · exact he.symm
  · have hb := Finset.card_le_card (reachableBound Symbol inst arity symbols S Gamma q ((vertices symbols S q).card+1))
    omega

theorem reachableSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (q : Packed Symbol arity Gamma) (n : Nat) : ∀ r,r∈reachable symbols S q n → WindowPrimary Symbol arity symbols S Gamma q r := by
  induction n with
  | zero => intro r hr; simp only [reachable,Finset.mem_singleton] at hr; subst r; exact .refl _
  | succ n ih =>
    intro r hr
    rcases (memStep symbols S q _ r).mp hr with hr | ⟨_,a,ha,he⟩
    · exact ih r hr
    · exact .trans (ih a ha) (NumberedPrimaryExchangeSupportProof.erase
        ((NumberedExchangeNeighborhoodProof.exchangeTestCorrect Symbol inferInstance arity symbols S hc Gamma a r).mp he))

theorem classClosed {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (q : Packed Symbol arity Gamma) (hq : InUniverse symbols S q.2)
    {a b : Packed Symbol arity Gamma} (ha : a∈primaryClass symbols S q)
    (hqa : WindowPrimary Symbol arity symbols S Gamma q a) (he : Exchange Symbol arity symbols S Gamma a b) :
    b∈primaryClass symbols S q := by
  have hqb : WindowPrimary Symbol arity symbols S Gamma q b := .trans hqa (NumberedPrimaryExchangeSupportProof.erase he)
  have hb := NumberedAuxiliaryDecodingProof.candidateCoverage Symbol inferInstance arity symbols S hc Gamma q b hq hqb
  have hv : b∈vertices symbols S q := Finset.mem_insert_of_mem (List.mem_toFinset.mpr hb)
  rw [← cardinalitySaturation Symbol inferInstance arity symbols S Gamma q]
  exact (memStep symbols S q _ b).mpr (Or.inr ⟨hv,a,ha,
    (NumberedExchangeNeighborhoodProof.exchangeTestCorrect Symbol inferInstance arity symbols S hc Gamma a b).mpr he⟩)

theorem chainComplete {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (q : Packed Symbol arity Gamma) (hq : InUniverse symbols S q.2)
    {a b : Packed Symbol arity Gamma} (h : Chain (Exchange Symbol arity symbols S Gamma) a b) :
    WindowPrimary Symbol arity symbols S Gamma q a → a∈primaryClass symbols S q → b∈primaryClass symbols S q := by
  induction h with
  | refl => intro _ ha; exact ha
  | step he => intro hqa ha; exact classClosed symbols S hc q hq ha hqa he
  | trans hab hbc ih1 ih2 =>
    intro hqa ha
    exact ih2 (.trans hqa (NumberedPrimaryExchangeProof.closureToPrimary hab)) (ih1 hqa ha)

theorem exactPrimaryClass : NumberedFinitePrimaryClassTargets.ActualExactPrimaryClass := by
  intro Symbol inst arity symbols S hc Gamma q hq r
  constructor
  · exact reachableSound symbols S hc q _ r
  · intro h
    exact chainComplete symbols S hc q hq (NumberedPrimaryExchangeProof.primaryToClosure h) (.refl _) (initialMember symbols S q _)

theorem primaryDecision : NumberedFinitePrimaryClassTargets.ActualPrimaryDecision := by
  intro Symbol inst arity symbols S hc Gamma q hq r
  simp only [primaryTest,decide_eq_true_eq]
  exact exactPrimaryClass Symbol inst arity symbols S hc Gamma q hq r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassProof
