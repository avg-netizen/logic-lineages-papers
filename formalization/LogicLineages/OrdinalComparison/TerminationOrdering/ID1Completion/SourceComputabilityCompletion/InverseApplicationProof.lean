module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward SourceComputabilityCompletion.InverseApplication
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalComputabilityDownwardProof InverseApplicationSyntaxProof
open InternalSliceInduction InternalSliceInductionProof
open InternalControlGraphSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (emb)
open GuardedSourceSyntaxProof (numeralRename)

theorem inverseAtElimination {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty) (a x f : OTerm α)
    (hi : Nonempty (Derivation body Gamma (inverseAt comp context sigma tau a x)))
    (hd : Nonempty (Derivation body Gamma (domain comp context sigma tau f a)))
    (ha : Nonempty (Derivation body Gamma (accepted comp sigma tau (numeral context) f a x))) :
    Nonempty (Derivation body Gamma (membership false f)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hd⟩ := hd
  obtain ⟨ha⟩ := ha
  have h := Derivation.universalElimination (emb f) hi
  rw [inverseAtInstance] at h
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hd ha)⟩

theorem inverseAtIntroduction {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty) (a x : OTerm α)
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (f : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (domain comp context sigma tau f (a.relabel j))) →
      Nonempty (Derivation body Delta
        (accepted comp sigma tau (numeral context) f (a.relabel j) (x.relabel j))) →
      Nonempty (Derivation body Delta (membership false f))) :
    Nonempty (Derivation body Gamma (inverseAt comp context sigma tau a x)) := by
  let P := domain comp context sigma tau (.var (.inr (0 : Fin 1))) (a.relabel Sum.inl) ⊓
    accepted comp sigma tau (numeral context) (.var (.inr (0 : Fin 1)))
      (a.relabel Sum.inl) (x.relabel Sum.inl)
  let Delta := P :: Gamma.map weaken
  have h : Derivation body Delta P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

theorem membershipIntroduction (src : SourcePresentation.Data) (context : Nat)
    {α : Type} {Gamma : List (Formula α)} (f : OTerm α)
    (hc : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (carrier src false context f)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (g : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (edge src false context (f.relabel j) g)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (membership false g))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (membership false f)) := by
  apply InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction src false context α Gamma f hc
  let P := edge src false context (f.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

theorem inverseSuccessorElimination {body : Positive (Fin 1)} {α : Type}
    {Gamma : List (Formula α)} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (a x y : OTerm α)
    (hs : Nonempty (Derivation body Gamma (inverseSuccessors src comp context sigma tau a x)))
    (he : Nonempty (Derivation body Gamma (edge src false context x y))) :
    Nonempty (Derivation body Gamma (inverseAt comp context sigma tau a y)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨he⟩ := he
  have h := Derivation.universalElimination (emb y) hs
  rw [inverseSuccessorInstance] at h
  exact ⟨Derivation.implicationElimination h he⟩

/-- The scalar induction step contracts one ORIGINAL application. Every
successor image comes from application totality and its original R lift. -/
theorem inverseAtFromSuccessors (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat)
    (rules : ArithmeticRules src comp context) (compatible : ApplicationCompatibility src comp context)
    (hcarrier : DomainCarrier src comp context) (hforward : DomainForward src comp context)
    {α : Type} {Gamma : List (Formula α)} (sigma tau : Ty) (a x : OTerm α)
    (hs : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (inverseSuccessors src comp context sigma tau a x))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (inverseAt comp context sigma tau a x)) := by
  apply inverseAtIntroduction comp context sigma tau a x
  intro β j Delta f hj hdomain haccept
  have hs' := renameInto hs j Delta hj
  rw [inverseSuccessorsRename] at hs'
  have hc := closedApply (hcarrier β sigma tau f (a.relabel j)) hdomain
  apply membershipIntroduction src context f hc
  intro γ k Omega g hk hedge
  have hd' := renameInto hdomain k Omega hk
  have ha' := renameInto haccept k Omega hk
  have hs'' := renameInto hs' k Omega hk
  simp only [domainRename,acceptedRename,numeralRename,inverseSuccessorsRename] at hd' ha' hs''
  have hdg := closedApply (hforward γ sigma tau (f.relabel k) g ((a.relabel j).relabel k))
    (conjunction hd' hedge)
  have ht := closedApply (rules.applicationTotal γ sigma tau g ((a.relabel j).relabel k)) hdg
  apply applicationCases comp context sigma tau g ((a.relabel j).relabel k)
    (membership false g) ht
  intro δ l Lambda out hl hout
  rw [membershipRename]
  have hd'' := renameInto hd' l Lambda hl
  have hg'' := renameInto hdg l Lambda hl
  have ha'' := renameInto ha' l Lambda hl
  have he'' := renameInto hedge l Lambda hl
  have hs''' := renameInto hs'' l Lambda hl
  simp only [domainRename,acceptedRename,numeralRename,edgeRename,inverseSuccessorsRename]
    at hd'' hg'' ha'' he'' hs'''
  have houtput := closedApply
    (compatible δ sigma tau ((f.relabel k).relabel l) (g.relabel l)
      (((a.relabel j).relabel k).relabel l) (((x.relabel j).relabel k).relabel l) out)
    (conjunction (conjunction hd'' he'') (conjunction ha'' hout))
  have hinverse := inverseSuccessorElimination src comp context sigma tau
    (((a.relabel j).relabel k).relabel l) (((x.relabel j).relabel k).relabel l)
    out hs''' houtput
  exact inverseAtElimination comp context sigma tau
    (((a.relabel j).relabel k).relabel l) out (g.relabel l) hinverse hg'' hout

theorem actualOriginalInverseApplication :
    InverseApplicationTargets.ActualOriginalInverseApplication := by
  intro src comp context rules compatible hcarrier hforward α Gamma sigma tau f a out hd ha hi
  let theta := inverseInvariant src comp context sigma tau a
  let R := replacedBody (sliceBody src context false) theta
  have hstep : Nonempty (Derivation (SourcePresentation.sourceBody src context) [R] theta) := by
    have h : Derivation (SourcePresentation.sourceBody src context) [R] R :=
      Derivation.hypothesis List.mem_cons_self
    change Derivation _ _
      (replacedBody (sliceBody src context false)
        (inverseInvariant src comp context sigma tau a)) at h
    rw [sliceEquation] at h
    have d := inverseAtFromSuccessors src comp context rules compatible hcarrier hforward
      sigma tau (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      ⟨Derivation.conjunctionRight h⟩
    exact d
  have hind := actualInternalSliceInduction src context α [] false theta out hstep
  change Nonempty (Derivation _ [] ((membership false out).imp (instantiate theta (emb out)))) at hind
  dsimp only [theta] at hind
  rw [invariantInstance] at hind
  exact inverseAtElimination comp context sigma tau a out f (closedApply hind hi) hd ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
