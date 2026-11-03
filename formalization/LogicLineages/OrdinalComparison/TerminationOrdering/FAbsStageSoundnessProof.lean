module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness ActualValueLogicalRelation CopyStatStageSoundness MarkedFAbsTest TypedObservationAccess

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem openingRelated (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types)
    (ha : InputRelated I above f P a base extras) (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i) :
    InputRelated I above f ⟨(i,σ)::P.val,h.2.1⟩ (openingInput f a σ υ i h)
      (renameArguments base (Renaming.weaken _ σ))
      (appendArguments (renameArguments extras (Renaming.weaken _ σ)) (.cons (.var .here) .nil)) := by
  let Q : World I := ⟨(i,σ)::P.val,h.2.1⟩
  let ext : Extends P Q := fun p hp => List.mem_cons_of_mem _ hp
  have hr : @Eq (Renaming (portTypes P.val++I.context) (σ::(portTypes P.val++I.context)))
      (LogicalRelationWorlds.portRename ext) (Renaming.weaken _ σ) := by
    funext τ v
    exact LiteralWorldTransportProof.consPortTransport Symbol inferInstance arity I P σ i h.2.1 τ v
  have hi := ConstructorInputLogicalRelationProof.inputWeakening Symbol inferInstance arity I above f P Q ext a base types extras ha
  have hb := congrArg (fun r : Renaming (portTypes P.val++I.context) (σ::(portTypes P.val++I.context)) => renameArguments base r) hr
  have he := congrArg (fun r : Renaming (portTypes P.val++I.context) (σ::(portTypes P.val++I.context)) => renameArguments extras r) hr
  have hi' : InputRelated I above f Q ((inputFamily I f).restrict ext a)
      (renameArguments base (Renaming.weaken _ σ)) (renameArguments extras (Renaming.weaken _ σ)) :=
    Eq.mp (congrArg₂ (fun (b : Arguments Symbol arity (σ::(portTypes P.val++I.context)) (headArguments arity f.val))
      (e : Arguments Symbol arity (σ::(portTypes P.val++I.context)) types) =>
      InputRelated I above f Q ((inputFamily I f).restrict ext a) b e) hb he) hi
  let values : FullListValueApplication.Values I [σ] Q := fun j => Fin.cases (LiteralVariableValueProof.variableValue (I := I) (P := Q) Variable.here) (fun k => Fin.elim0 k) j
  let args : Arguments Symbol arity (portTypes Q.val++I.context) [σ] := .cons (.var .here) .nil
  have hv : ∀ j,Related I above ([σ].get j) Q (values j) (argumentAt args j) := by
    intro j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact LogicalRelationWorldsProof.literalVariableRelated Symbol inferInstance arity I above σ Q Variable.here
  have ht : ∀ τ ∈ [σ],τ ∈ TypedExtraDownsets.types I := by
    intro τ hτ
    rcases List.mem_singleton.mp hτ with rfl
    exact h.2.2.1
  have H := ConstructorInputLogicalRelationProof.inputAppend Symbol inferInstance arity I above f Q _
    (renameArguments base (Renaming.weaken _ σ)) types (renameArguments extras (Renaming.weaken _ σ)) [σ] ht values args hi' hv
  have hpack : FunctionalSpineActions.packArguments [σ] ht values=
      [⟨⟨σ,h.2.2.1⟩,LiteralVariableValueProof.variableValue (I := I) (P := Q) Variable.here⟩] := by
    simp only [FunctionalSpineActions.packArguments,List.ofFn_succ,List.ofFn_zero]
    rfl
  exact Eq.mp (congrArg (fun ps : List (TypedExtraDownsets.Packed I Q) =>
    InputRelated I above f Q (FunctionalTupleBuilder.appendInput ((inputFamily I f).restrict ext a) ps)
      (renameArguments base (Renaming.weaken _ σ))
      (appendArguments (renameArguments extras (Renaming.weaken _ σ)) args)) hpack) H

theorem lambdaSound (above : Symbol → Symbol → Prop) (M : Constructors I) (hM : FamilySound I above M)
    (f : HeadIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types)
    (ha : InputRelated I above f P a base extras) (σ υ : Ty)
    (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ)
    (ho : (⟨P.val,.arrow σ υ,.lam body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target)
    (hb : fAbsTest M f a ⟨P.val,.arrow σ υ,.lam body⟩=true) :
    Weak Symbol arity above (portTypes P.val++I.context)
      ⟨.arrow σ υ,.marked f.val (.arrow σ υ) base types extras⟩ ⟨.arrow σ υ,embed (.lam body)⟩ := by
  rw [MarkedFAbsTestProof.literalLambdaEquation Symbol inferInstance arity I M f P σ υ body a] at hb
  obtain ⟨i,h,hread⟩ := (MarkedFAbsTestProof.lambdaCalibration Symbol inferInstance arity I M f P σ υ body a).mp hb
  have hobs := (MarkedFAbsTestProof.genuineOpeningGuards Symbol inferInstance arity I P σ υ body i ho h.1).2
  have hi := openingRelated above f P a base types extras ha σ υ i h
  have hrel := hM f ⟨υ,h.2.2.2⟩ ⟨(i,σ)::P.val,h.2.1⟩ (openingInput f a σ υ i h)
    (renameArguments base (Renaming.weaken _ σ)) (types++[σ])
    (appendArguments (renameArguments extras (Renaming.weaken _ σ)) (.cons (.var .here) .nil)) hi
  let o : ObservationAt I υ ⟨(i,σ)::P.val,h.2.1⟩ := ⟨⟨(i,σ)::P.val,υ,body⟩,hobs,rfl,rfl⟩
  exact Weak.fAbs f.val base types extras (embed body)
    (SelectStageSoundnessProof.relatedWeakCurrent above _ _ hrel o hread)

theorem fAbsSound : FAbsStageSoundnessTargets.FAbsSound := by
  intro Symbol inst arity I above dec M f τ P a base types extras o hM ha hb
  rcases τ with ⟨τ,hτ⟩
  rcases o with ⟨⟨ports,υ,body⟩,hom,hp,ht⟩
  dsimp at hp ht
  subst ports
  subst υ
  cases body <;> try (simp [fAbsTest,bodyAtWorld,termTest] at hb)
  case lam body => exact lambdaSound above M hM f P a base types extras ha _ _ body hom ((MarkedFAbsTestProof.literalLambdaEquation Symbol inst arity I M f P _ _ body a).trans hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessProof
