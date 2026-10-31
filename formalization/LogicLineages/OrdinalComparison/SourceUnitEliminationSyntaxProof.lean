module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationTargets
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProof
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitElimination.Proof
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem program_values_computable : Computable programValues := by
  let f := AbsoluteObserver.openSourceValue
  have hf : Computable f := AbsoluteObserver.Proof.open_evaluator_computable
  let prefixValues (xs : List (Nat×Nat)) (n : Nat) := (List.range n).map (fun i => f (xs.getD i (0,0)))
  have hstep : Computable (fun p : (List (Nat×Nat) × Nat) × (Nat × List Nat) =>
      p.2.2 ++ [f (p.1.1.getD p.2.1 (0,0))]) :=
    Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp ((Primrec.list_getD (0,0)).to_comp.comp
        (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)))
  have hr := Computable.nat_rec (Computable.snd : Computable (fun p : List (Nat×Nat) × Nat => p.2))
    (Computable.const ([] : List Nat)) hstep.to₂
  have hp : Computable₂ prefixValues := by
    apply hr.of_eq
    intro p
    rcases p with ⟨xs,n⟩
    induction n with
    | zero => rfl
    | succ n ih => simp only [prefixValues,List.range_succ,List.map_append,List.map_singleton,Nat.rec_add_one,ih]
  apply (hp.comp Computable.id Computable.list_length).of_eq
  intro xs
  change prefixValues xs xs.length=xs.map f
  apply List.ext_getElem
  · simp [prefixValues]
  · intro i hi hj
    have hix : i<xs.length := by simpa [prefixValues] using hi
    simp [prefixValues,List.getD_eq_getElem?_getD,hix]

theorem map_anchors {α β : Type} (f : α → β) {Γ} (q : Tree α Γ) :
    anchors (mapAnchors f q)=(anchors q).map f := by
  induction q with
  | leaf b => rfl
  | free left right σ d q ih => exact ih
  | active left right σ p d d' c q r ihq ihr =>
    simp only [mapAnchors,anchors,ihq,ihr,List.map_append]

theorem realize_anchors (Γ : List Ty) (q : Tree (Nat×Nat) Γ) :
    anchors (realize q)=programValues (anchors q) := map_anchors _ q

theorem all_sources_ground {α : Type} {Γ} (q : Tree α Γ) :
    ∀ s ∈ sources q, ∀ σ ∈ s.1, σ=Ty.ground := by
  induction q with
  | leaf b =>
    intro s hs
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl
    · exact AbsoluteObserver.Proof.two_ground b.allGround
    · exact AbsoluteObserver.Proof.two_ground b.allGround
  | free left right σ d q ih => exact ih
  | active left right σ p d d' c q r ihq ihr =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ihq s hs
    · exact ihr s hs

theorem valuation_inputs {Γ} (ρ : Variable Γ .ground → Nat) :
    valuation (UnitObservation.substitution ρ)=(fun c => ((inputs ρ c+1 : Nat) : Ordinal)) := by
  funext c
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground =>
    have hj : j=0 := Fin.eq_zero j
    subst j
    exact (UnitObservation.Proof.groundValue Γ ρ x).2
  | arrow a b =>
    have hx := UnitObservation.Proof.functionalCoordinates Γ ρ (.arrow a b)
      (by simp only [Ty.level]; omega) x j
    change closedValue ((UnitObservation.substitution ρ).vector x j)=_
    rw [hx]
    simp only [closedValue,denote,inputs,Nat.zero_add,Nat.cast_one]

def RawGraph {Γ τ} (t : OriginalTerm Γ τ) (ρ : Variable Γ .ground → Nat) (r : Nat) : Prop :=
  ∃ v : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
    expressionValue (UnitObservation.substitution ρ) (v 0)=(r : Ordinal)

theorem ground_leaf {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : OriginalTerm Γ τ)
    (ρ : Variable Γ .ground → Nat) (r : Nat) :
    Eval (realize (.leaf (groundBlock hΓ t))) ρ r ↔ RawGraph t ρ r := by
  obtain ⟨w,s,hw,hs,hcode,hclosed,hopen,hpos,hvalue⟩ := AbsoluteObserver.Proof.anchorCorrect Γ hΓ τ t
  have he : Eval (realize (.leaf (groundBlock hΓ t))) ρ r ↔
      AbsoluteObserver.Formula hΓ t (inputs ρ) r := by
    simp only [realize,mapAnchors,groundBlock,Eval,AbsoluteObserver.Formula]
    rw [hopen]
  rw [he,AbsoluteObserver.Proof.fullAbsoluteObserver.2.2.2.2 Γ hΓ τ t (inputs ρ) r]
  unfold RawGraph expressionValue
  rw [valuation_inputs]
end LogicLineages.OrdinalComparison.Source.UnitElimination.Proof
