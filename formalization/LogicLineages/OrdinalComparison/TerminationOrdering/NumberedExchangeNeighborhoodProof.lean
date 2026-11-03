module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedPrimaryExchange NumberedExchangeNeighborhood NumberedExchangeNeighborhoodSupportProof

theorem typedListReconstruction : NumberedExchangeNeighborhoodTargets.ActualTypedListReconstruction :=
  NumberedExchangeNeighborhoodSupportProof.typedListReconstruction

theorem neighborsSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (q : AuxTerm Symbol arity Gamma tau) : ∀ r,r∈neighbors symbols S q → Exchange Symbol arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩ := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ target,target∈argumentNeighbors symbols S args → ArgumentExchange Symbol arity symbols S Gamma types args target)
  case var => intro r h; simp [neighbors] at h
  case bottom => intro r h; simp [neighbors] at h
  case lam body ih =>
    intro r h
    obtain ⟨b,hb,hr⟩ := List.mem_map.mp h
    cases hr
    exact .lam body b (ih b hb)
  case app q a ihq iha =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨f,hf,hr⟩ := List.mem_map.mp h
      cases hr
      exact .appFunction q f a (ihq f hf)
    · obtain ⟨b,hb,hr⟩ := List.mem_map.mp h
      cases hr
      exact .appArgument q a b (iha b hb)
  case ordinary f base ih =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · exact ordinarySound symbols S hc f base r h
    · obtain ⟨target,ht,hr⟩ := List.mem_map.mp h
      cases hr
      exact .ordinaryArguments f base target (ih target ht)
  case numbered k f tau base types extras ihb ihe =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact numberedSound symbols S hc k f tau base types extras r h
      · obtain ⟨target,ht,hr⟩ := List.mem_map.mp h
        cases hr
        exact .numberedBase k f tau base target types extras (ihb target ht)
    · obtain ⟨target,ht,hr⟩ := List.mem_map.mp h
      cases hr
      exact .numberedExtras k f tau base types extras target (ihe target ht)
  case nil Gamma target h => simp [argumentNeighbors] at h
  case cons Gamma sigma types q rest ihq ihr target h =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r,hr,ht⟩ := List.mem_map.mp h
      cases ht
      exact .head q r rest (ihq r hr)
    · obtain ⟨tail,hr,ht⟩ := List.mem_map.mp h
      cases ht
      exact .tail q rest tail (ihr tail hr)

theorem complete {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    {q r : Packed Symbol arity Gamma} (h : Exchange Symbol arity symbols S Gamma q r) :
    ∃ target,target∈neighbors symbols S q.2 ∧ (⟨q.1,target⟩ : Packed Symbol arity Gamma)=r := by
  induction h using Exchange.rec
    (motive_2 := fun Gamma types a b _ => b∈argumentNeighbors symbols S a)
  case ordinary f g base target hf hg he ht hp =>
    obtain ⟨r,hr,heq⟩ := ordinaryComplete symbols S hc f g base target hf hg he ht hp
    exact ⟨r,List.mem_append_left _ hr,heq⟩
  case numbered k f g tau base target types extras hf hg he hp =>
    exact ⟨_,List.mem_append_left _ (List.mem_append_left _ (numberedComplete symbols S hc k f g tau base target types extras hf hg he hp)),rfl⟩
  case lam q r h ih =>
    obtain ⟨r',hr,he⟩ := ih
    have heq : r'=r := eq_of_heq (Sigma.mk.inj he).2
    subst r'
    exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,rfl⟩
  case appFunction q r a h ih =>
    obtain ⟨r',hr,he⟩ := ih
    have heq : r'=r := eq_of_heq (Sigma.mk.inj he).2
    subst r'
    exact ⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨r,hr,rfl⟩),rfl⟩
  case appArgument q a b h ih =>
    obtain ⟨b',hb,he⟩ := ih
    have heq : b'=b := eq_of_heq (Sigma.mk.inj he).2
    subst b'
    exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩),rfl⟩
  case ordinaryArguments f base target h ih =>
    exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨target,ih,rfl⟩),rfl⟩
  case numberedBase k f tau base target types extras h ih =>
    exact ⟨_,List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨target,ih,rfl⟩)),rfl⟩
  case numberedExtras k f tau base types extras target h ih =>
    exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨target,ih,rfl⟩),rfl⟩
  case head q r rest h ih =>
    obtain ⟨r',hr,he⟩ := ih
    have heq : r'=r := eq_of_heq (Sigma.mk.inj he).2
    subst r'
    exact List.mem_append_left _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  case tail q rest target h ih =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨target,ih,rfl⟩)

theorem termNeighborhood : NumberedExchangeNeighborhoodTargets.ActualTermNeighborhood := by
  intro Symbol inst arity symbols S hc Gamma tau q r
  constructor
  · exact neighborsSound symbols S hc q r
  · intro h
    obtain ⟨r',hr,he⟩ := complete symbols S hc h
    have heq : r'=r := eq_of_heq (Sigma.mk.inj he).2
    exact heq ▸ hr

theorem argumentNeighborhood : NumberedExchangeNeighborhoodTargets.ActualArgumentNeighborhood := by
  intro Symbol inst arity symbols S hc Gamma types args target
  induction types with
  | nil => cases args; cases target; constructor <;> intro h
           · simp [argumentNeighbors] at h
           · cases h
  | cons sigma types ih =>
    cases args with
    | cons q rest =>
      constructor
      · intro h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨r,hr,ht⟩ := List.mem_map.mp h
          cases ht
          exact .head q r rest ((termNeighborhood Symbol inst arity symbols S hc Gamma sigma q r).mp hr)
        · obtain ⟨tail,hr,ht⟩ := List.mem_map.mp h
          cases ht
          exact .tail q rest tail ((ih rest tail).mp hr)
      · intro h
        cases h with
        | head q r rest h => exact List.mem_append_left _ (List.mem_map.mpr ⟨r,(termNeighborhood Symbol inst arity symbols S hc Gamma sigma q r).mpr h,rfl⟩)
        | tail q rest target h => exact List.mem_append_right _ (List.mem_map.mpr ⟨target,(ih rest target).mpr h,rfl⟩)

theorem exchangeTestCorrect : NumberedExchangeNeighborhoodTargets.ActualExchangeTest := by
  intro Symbol inst arity symbols S hc Gamma q r
  simp only [exchangeTest,decide_eq_true_eq,List.mem_map]
  constructor
  · rintro ⟨target,ht,he⟩
    cases he
    exact neighborsSound symbols S hc q.2 target ht
  · exact complete symbols S hc

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodProof
