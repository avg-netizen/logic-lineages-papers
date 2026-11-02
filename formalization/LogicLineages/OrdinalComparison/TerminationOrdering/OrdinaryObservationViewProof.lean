module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer OrdinaryObservationView

theorem packedCalibration {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (p : RecursiveComparison.Packed Symbol arity Γ) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)) :
    packedView p=some ⟨f,base⟩ ↔ p=⟨headResult f,.ordinary f base⟩ := by
  constructor
  · intro h
    rcases p with ⟨τ,q⟩
    cases q with
    | ordinary g args =>
        have he : (⟨g,args⟩ : RootData Symbol arity Γ)=⟨f,base⟩ := Option.some.inj h
        cases he
        rfl
    | var v => simp [packedView] at h
    | lam body => simp [packedView] at h
    | marked g σ args extraTypes extras => simp [packedView] at h
  · rintro rfl
    rfl

theorem rootCalibration : OrdinaryObservationViewTargets.RootCalibration := by
  intro Symbol arity Γ τ t f base
  exact packedCalibration _ f base

theorem childEmbedding {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) :
    (childTerms t).map embedChild=GuardedQueryGraphSupportProof.ordinaryArguments ⟨τ,embed t⟩ := by
  cases t <;> try rfl
  case ranked s args =>
    simp only [childTerms,List.map_ofFn,embed,GuardedQueryGraphSupportProof.ordinaryArguments]
    exact (GuardedQueryGraphSupportProof.groundPacked (arity s) (fun i => embed (args i))).symm

theorem argumentCalibration : OrdinaryObservationViewTargets.ArgumentCalibration := by
  intro Symbol arity Γ τ t f base h
  have hc := childEmbedding t
  rw [(rootCalibration Symbol arity Γ τ t f base).mp h] at hc
  exact hc

theorem argumentTypes {Symbol : Type} {arity : Symbol → Nat} {Γ ts : List Ty}
    (args : Arguments Symbol arity Γ ts) : (RecursiveComparison.argumentList args).map Sigma.fst=ts := by
  induction ts with
  | nil => cases args; rfl
  | cons τ ts ih =>
      cases args with
      | cons q rest => simp only [RecursiveComparison.argumentList,List.map_cons,ih rest]

theorem argumentTypeCalibration : OrdinaryObservationViewTargets.ArgumentTypeCalibration := by
  intro Symbol arity Γ τ t f base h
  have he := congrArg (List.map Sigma.fst) (argumentCalibration Symbol arity Γ τ t f base h)
  simpa only [List.map_map,embedChild,Function.comp_def,argumentTypes] using he

theorem plainChildrenCalibration : OrdinaryObservationViewTargets.PlainChildrenCalibration := by
  intro Symbol arity Γ B o
  rcases o with ⟨P,τ,t⟩
  cases t <;> try rfl
  case ranked s args =>
    simp only [childTerms,List.map_ofFn,plainChildren]
    rfl

theorem childProvenance : OrdinaryObservationViewTargets.ChildProvenance := by
  intro Symbol arity I o c ho hc
  have hc' : c ∈ plainChildren o := by rw [←plainChildrenCalibration Symbol arity I.context (budget I) o]; exact hc
  have hm := Source.SourceOpenedObservationsProof.openedPlainChildClosure Symbol arity I.context I.targetType I.target (budget I) o c ho hc'
  refine ⟨hm,?_,?_⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    rfl
  · apply Finset.mem_union_right
    exact Source.SourceOpenedObservationsProof.openedTypeSupport Symbol arity I.context I.targetType I.target (budget I) c hm
      (Source.SourceTypeSupportProof.actualResultSupport Symbol arity _ c.resultType c.body)

theorem declaredArgumentTypes : OrdinaryObservationViewTargets.DeclaredArgumentTypes := by
  intro Symbol arity I o f base ho hv υ hυ
  rw [←argumentTypeCalibration Symbol arity _ o.resultType o.body f base hv] at hυ
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hυ
  have hc := (childProvenance Symbol arity I o (observeChild o.ports p) ho (List.mem_map.mpr ⟨p,hp,rfl⟩)).2.2
  simpa only [observeChild,he] using hc

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewProof
