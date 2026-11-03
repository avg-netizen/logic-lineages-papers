module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessFreshProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessInductionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness RenamingEquivariance ActualComparisonCompletenessSupportProof ActualComparisonCompletenessOrdinaryProof ActualComparisonCompletenessSelectProof ActualComparisonCompletenessFreshProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem markCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {τ : Ty}
    (s r t : MarkedTerm Symbol arity Γ τ) (hm : strictMark s=some r)
    (ih : Meaning (I := I) above false ⟨τ,r⟩ ⟨τ,t⟩) : Meaning (I := I) above true ⟨τ,s⟩ ⟨τ,t⟩ := by
  intro P rename hs o ho hp he
  have hr := ActualStrictMarkSupportProof.markConfined s hs r hm
  exact (ActualStrictMarkProof.markBitEquality Symbol inferInstance arity I above inferInstance Γ τ ⟨s,hs⟩ r hr hm P
    (reindex rename (identity I P)) o).trans (ih P rename hr o ho hp he)

theorem weakMeaning (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {s t : RecursiveComparison.Packed Symbol arity Γ} (h : Weak Symbol arity above Γ s t) :
    Meaning (I := I) above false s t := by
  induction h using Weak.rec
    (motive_2 := fun Γ s t _ => Meaning (I := I) above true s t)
    (motive_3 := fun Γ ss ts _ => List.Forall₂ (Meaning (I := I) above false) ss ts)
    (motive_4 := fun Γ ss ts _ => MultiMeaning (I := I) above ss ts)
    (motive_5 := fun Γ ss ts _ => ∀ t ∈ ts,∃ s ∈ ss,Meaning (I := I) above true s t)
  case var v => exact varCase above v
  case abs s t hw ih => exact absCase above s t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact funCase above f g ss ts matched he ht hp ih
  case put f ss t hw ih => exact putCase above f ss t ih
  case select f ss extraTypes extras types q r t suffix hmem happ hw ih =>
    exact selectCase above f ss extraTypes extras types q r t suffix hmem happ ih
  case fAbs f ss extraTypes extras t hw ih => exact fAbsCase above f ss extraTypes extras t ih
  case copy f g ss extraTypes extras ts ha hw ih => exact copyCase above f g ss extraTypes extras ts ha ih
  case stat f g ss extraTypes extras ts he hm hw ihm ihw => exact statCase above f g ss extraTypes extras ts he ihm ihw
  case mark s r t hm hw ih => exact markCase above s r t hm ih
  case nil => exact .nil
  case cons s t ss ts hw hm ihw ihm => exact .cons ihw ihm
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr =>
    exact ⟨kept,removed,retained,inserted,hp,hq,hn,ihw,ihr⟩
  case nil Γ removed =>
    intro removedList t ht
    simp at ht
  case cons Γ removed s t rest hs hst hr ihst ihr =>
    intro ihTail u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨t,hst,ihr⟩
    · exact ihTail u hu

theorem strictMeaning (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {s t : RecursiveComparison.Packed Symbol arity Γ} (h : Strict Symbol arity above Γ s t) :
    Meaning (I := I) above true s t := by
  cases h with
  | mark s r t hm hw => exact markCase above s r t hm (weakMeaning above hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessInductionProof
