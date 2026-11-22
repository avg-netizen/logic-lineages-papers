module
public import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchTargets
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxRankProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualRankedNormalizationSyntax (AgreeThrough normalizedTerms exactOriginalRankReadLocality)
open ActualFullValueLabels (Label labels exactFullValueLabels)
open ActualFullLabelPairGuards (Pair Answer ActualOutcome)
open ActualFiniteFullValueGuards (Matches pairs)
open ActualFullValueMaximalMetadata (exactActualMaximalMetadata)
open ActualMixedRowLeadingAnnotations (CountTailReady AlignedAnnotations fullValues)
open ActualMixedRowLeadingSum (rowParts)
open ActualReadChargeIteration (ReadState ChosenClass RankBound)
open ActualZeroClassReplacement (Read liftedReads)

theorem supported (r top : Nat) (raw : List WeightedOperand) (rs : List Read)
    (literal : rs.map Prod.fst = raw)
    (scope : ∀ t ∈ raw, t.2.rank < r ∧ t.2.rank ≤ top) :
    ∀ rd ∈ rs, rd.1.2.rank < r ∧ rd.1.2.rank ≤ top := by
  intro rd used
  apply scope rd.1
  rw [← literal]
  exact List.mem_map.mpr ⟨rd,used,rfl⟩

theorem readTransport (f ρ σ : Nat → Nat) (top : Nat) (agreed : AgreeThrough ρ σ top)
    (rs : List Read) (scope : ∀ rd ∈ rs, rd.1.2.rank ≤ top) :
    liftedReads f ρ rs ↔ liftedReads f σ rs := by
  apply (exactOriginalRankReadLocality f ρ σ top agreed).2.1
  intro t used
  obtain ⟨rd,here,rfl⟩ := List.mem_map.mp used
  exact scope rd here

theorem matchedTransport (f ρ σ : Nat → Nat) (top : Nat) (agreed : AgreeThrough ρ σ top)
    (ls : List Label) (range : ∀ l ∈ ls, l.rank ≤ top) (as : List Answer) :
    Matches f ρ (pairs ls) as ↔ Matches f σ (pairs ls) as := by
  have label := (exactOriginalRankReadLocality f ρ σ top agreed).2.2.1
  have scope (p : Pair) (used : p ∈ pairs ls) : p.1.rank ≤ top ∧ p.2.rank ≤ top := by
    obtain ⟨l,hl,inside⟩ := List.mem_flatMap.mp used
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp inside
    exact ⟨range l hl,range r hr⟩
  have equiv (ps : List Pair) (within : ∀ p ∈ ps, p.1.rank ≤ top ∧ p.2.rank ≤ top)
      (as : List Answer) : Matches f ρ ps as ↔ Matches f σ ps as := by
    induction ps generalizing as with
    | nil =>
        cases as with
        | nil => exact ⟨fun _ => .nil,fun _ => .nil⟩
        | cons a as =>
            constructor <;> intro h <;> cases h
    | cons p ps ih =>
        cases as with
        | nil =>
            constructor <;> intro h <;> cases h
        | cons a as =>
            have range := within p List.mem_cons_self
            have head : ActualOutcome f ρ p a ↔ ActualOutcome f σ p a := by
              constructor
              · rintro ⟨u,v,l,r,ans⟩
                exact ⟨u,v,(label p.1 range.1 u).mp l,(label p.2 range.2 v).mp r,ans⟩
              · rintro ⟨u,v,l,r,ans⟩
                exact ⟨u,v,(label p.1 range.1 u).mpr l,(label p.2 range.2 v).mpr r,ans⟩
            have tail := ih (fun q hq => within q (List.mem_cons_of_mem _ hq)) as
            constructor
            · intro h
              cases h with
              | cons first rest => exact .cons (head.mp first) (tail.mp rest)
            · intro h
              cases h with
              | cons first rest => exact .cons (head.mpr first) (tail.mpr rest)
  exact equiv _ scope as

private theorem rightEmpty {α β : Type} {rel : α → β → Prop} (rs : List β)
    (h : List.Forall₂ rel [] rs) : rs = [] := by
  cases h
  rfl

theorem chosenCoefficient (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (θ : Nat → Nat) (top : Nat) (raw : List WeightedOperand) (a : List Answer) (xs : List Read)
    (frames : xs.map Prod.fst = normalizedTerms raw)
    (guards : StaticGuards B θ raw)
    (matched : Matches f θ (pairs (nodeLabels raw)) a)
    (anns : List ActualMixedRowLeadingAnnotations.Annotation) (C : Nat)
    (chosen : ChosenClass f θ top xs anns C) :
    nodeCoefficient raw a = (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) anns).1 := by
  let terms := xs.map Prod.fst
  let values := xs.map Prod.snd
  have countReady : ∀ t ∈ terms, t.1 ≠ 0 → CountTailReady θ t.2 := by
    intro t used nz
    have same : t ∈ normalizedTerms raw := by simpa only [terms,frames] using used
    exact guards.1 t same nz
  have aligned := exactFullValueLabels f B hf θ terms values anns chosen.1 countReady
  have live : labels terms ≠ [] := by
    intro empty
    rw [empty] at aligned
    have valuesEmpty : fullValues f anns = [] := rightEmpty _ aligned
    have impossible := chosen.2.1
    rw [valuesEmpty] at impossible
    cases impossible
  have agrees : Matches f θ (pairs (labels terms)) a := by simpa only [terms,frames,nodeLabels] using matched
  obtain ⟨D,found,_,weight,_⟩ :=
    exactActualMaximalMetadata f B hf θ terms values anns chosen.1 countReady live a agrees
  have same : D = C := Option.some.inj (found.symm.trans chosen.2.1)
  rw [same] at weight
  simpa only [nodeCoefficient,terms,frames] using weight

end LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
