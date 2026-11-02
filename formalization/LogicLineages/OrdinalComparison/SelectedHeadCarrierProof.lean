module
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierTargets
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.Proof
open ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof

theorem selectedActivity : Targets.SelectedActivity := by
  intro k Γ F q h hs
  induction hs with
  | here ha => exact ha
  | addLeft hs ih =>
    change _ ∈ names (.add _ _)
    rw [names_add,List.mem_append]
    exact Or.inl ih
  | addRight hs ih =>
    change _ ∈ names (.add _ _)
    rw [names_add,List.mem_append]
    exact Or.inr ih
  | tail hs ih =>
    change _ ∈ names (.collapse _ _)
    rw [names_collapse,List.mem_append]
    exact Or.inr ih

theorem operatorExtraction : Targets.OperatorExtraction := by
  intro k Γ F p q h hq
  induction hq generalizing h with
  | free hn =>
    intro hs
    exact False.elim (hn (selectedActivity k Γ F _ h hs))
  | tracked => intro hs; cases hs
  | add ha hb iha ihb =>
    intro hs
    cases hs with
    | addLeft hs => exact iha _ hs
    | addRight hs => exact ihb _ hs
  | collapse op support ht ih =>
    intro hs
    cases hs with
    | here _ => exact op
    | tail hs => exact ih _ hs

theorem actualSelectedCarriers : Targets.ActualSelectedCarriers := by
  intro k Γ n e
  obtain ⟨u,hu,hq⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  refine ⟨u,hu,?_⟩
  intro h hs
  obtain ⟨r,t,ou,hot,hoh⟩ := operatorExtraction k _ .here OrdinalSyntax.defaultPolicy (u 0) h hq hs
  obtain ⟨ou',w,v,hot',hw,hv,heq,hscalar,hvalue⟩ := UnaryCarrier.Proof.actualCarrier Γ k r t
  have heu : ou' = ou := Option.some.inj (hot'.symm.trans hot)
  subst ou'
  refine ⟨r,t,ou,w,v,hot,hoh,hw,hv,heq,hscalar,?_,?_⟩
  · exact fun x => UnaryCarrier.Proof.carrier_no_ground t x
  · intro ρ μ
    simpa only [hoh] using hvalue ρ μ
end LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier.Proof
