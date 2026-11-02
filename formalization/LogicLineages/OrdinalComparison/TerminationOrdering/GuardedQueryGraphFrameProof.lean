module
public import LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphFrameProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives GuardedQueryGraph
open FiniteQueryPrimitivesSupportProof GuardedQueryGraphSupportProof ComparisonFreeVariablesSyntaxProof

theorem appendTypes {Symbol : Type} {arity : Symbol → Nat} {Γ types more : List Ty}
    (K : Ty → Prop) (args : Arguments Symbol arity Γ types) (tail : Arguments Symbol arity Γ more)
    (h : argumentTypesAllowed K args) (ht : argumentTypesAllowed K tail) :
    argumentTypesAllowed K (appendArguments args tail) := by
  induction types with
  | nil => cases args; exact ht
  | cons σ types ih => cases args with
    | cons q rest => exact ⟨h.1,ih rest h.2⟩

theorem appendHeads {Symbol : Type} {arity : Symbol → Nat} {Γ types more : List Ty}
    (P : Head Symbol → Prop) (args : Arguments Symbol arity Γ types) (tail : Arguments Symbol arity Γ more)
    (h : argumentsAllowed P args) (ht : argumentsAllowed P tail) :
    argumentsAllowed P (appendArguments args tail) := by
  induction types with
  | nil => cases args; exact ht
  | cons σ types ih => cases args with
    | cons q rest => exact ⟨h.1,ih rest h.2⟩

theorem openBounds {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Γ) (hc : SubtypeClosed K)
    (f : Head Symbol) (σ τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types)
    (hk : typesAllowed K (.marked f (.arrow σ τ) base types extras))
    (hp : headsAllowed P (.marked f (.arrow σ τ) base types extras))
    (ha : Supported (.marked f (.arrow σ τ) base types extras) a) :
    typesAllowed K (openMarked f σ τ base types extras) ∧
    headsAllowed P (openMarked f σ τ base types extras) ∧
    Supported (openMarked f σ τ base types extras) (liftAllowed a) := by
  have hσ : K σ := hc _ hk.1 _ (by simp [Ty.subtypes,Ty.mem_subtypes_self])
  have hτ : K τ := hc _ hk.1 _ (by simp [Ty.subtypes,Ty.mem_subtypes_self])
  have hkr := TypeClosureProof.renamingTypeClosure Symbol arity K Γ (σ::Γ) _
    (.marked f (.arrow σ τ) base types extras) (Renaming.weaken Γ σ) hk
  have hpr := LogicLineages.OrdinalComparison.TerminationOrdering.Proof.renamingHeadClosure Symbol arity P Γ (σ::Γ) _
    (.marked f (.arrow σ τ) base types extras) (Renaming.weaken Γ σ) hp
  refine ⟨⟨hτ,hkr.2.1,appendTypes K _ _ hkr.2.2 ⟨hσ,trivial⟩⟩,
    ⟨hpr.1,hpr.2.1,appendHeads P _ _ hpr.2.2 ⟨trivial,trivial⟩⟩,?_,?_⟩
  · exact renameArgumentsSupported base a (liftAllowed a) (Renaming.weaken Γ σ) ha.1 (by intros; assumption)
  · apply (appendSupported _ _ (liftAllowed a)).mpr
    exact ⟨renameArgumentsSupported extras a (liftAllowed a) (Renaming.weaken Γ σ) ha.2 (by intros; assumption),⟨trivial,trivial⟩⟩

theorem argumentFrame {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) (P : PortContext (lambdaDepth t))
    (source : Packed Symbol arity (portTypes P++Γ)) (g : Head Symbol)
    (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
    (hf : GuardedQueryGraph.Frame s t (queryAt .weak P source ⟨_,.ordinary g ts⟩))
    (types : List Ty) (args : Arguments Symbol arity (portTypes P++Γ) types)
    (hk : argumentTypesAllowed (fun υ => υ ∈ inputTypes s t) args)
    (hh : argumentsAllowed (fun h => h ∈ markedHeads (embed s)) args)
    (ha : ArgumentsSupported args (liftAllowedList (inputNames s t) (portTypes P)))
    (p q : Packed Symbol arity (portTypes P++Γ)) (hp : p ∈ argumentList args) (hq : q ∈ argumentList ts) (mode : Mode) :
    GuardedQueryGraph.Frame s t (queryAt mode P p q) := by
  exact ⟨(argumentTypeMembership _ args).mp hk p hp,(argumentHeadMembership _ args).mp hh p hp,
    (argumentsListSupported args _).mp ha p hp,targetChildObservation s t .weak P source g ts hf q hq⟩

theorem retypedFrame {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) (P : PortContext (lambdaDepth t))
    (f g : Head Symbol) (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
    (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
    (hf : GuardedQueryGraph.Frame s t (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩))
    (p : Packed Symbol arity (portTypes P++Γ)) (hp : p ∈ argumentList ts) :
    GuardedQueryGraph.Frame s t (queryAt .weak P ⟨p.1,.marked f p.1 base types extras⟩ p) := by
  obtain ⟨u,hu,ho⟩ := targetChildObservation s t .weak P _ g ts hf p hp
  exact ⟨⟨observationType s t P p.1 u ho,hf.1.2⟩,hf.2.1,hf.2.2.1,u,hu,ho⟩

theorem stepPreservesFrame : GuardedQueryGraphTargets.StepPreservesFrame := by
  intro Symbol arity above Γ σ τ s t q r hf hstep
  have hc := (FiniteQueryPrimitivesProof.initialFrame Symbol arity Γ σ τ s t).1
  cases hstep with
  | mark P source marked target hm =>
      have he := RecursiveComparisonProof.strictMarkHelperAgreement Symbol arity _ _ source
      refine ⟨TypeClosureProof.markingTypeClosure Symbol arity _ _ _ source marked hf.1 (he marked hm),
        LogicLineages.OrdinalComparison.TerminationOrdering.Proof.markingHeadClosure Symbol arity _ _ _ source marked hf.2.1 (he marked hm),
        markSupported source marked hm _ hf.2.2.1,hf.2.2.2⟩
  | put P f base target => exact ⟨⟨hf.1.1,hf.1.2,trivial⟩,⟨hf.2.1.1,hf.2.1.2,trivial⟩,⟨hf.2.2.1,trivial⟩,hf.2.2.2⟩
  | abs P α β source body i hi =>
      obtain ⟨ordinary,hbody,hfresh,hopened⟩ := freshOpeningAvailability Symbol arity Γ σ τ s t .weak P _ α β body hf
      exact ⟨hf.1.2.2,hf.2.1,hf.2.2.1,ordinary,hbody,hopened i hi⟩
  | funPair P f g ss ts matched a b he ht hp hmem =>
      obtain ⟨ha,hb⟩ := zipMembers hmem
      exact argumentFrame s t P _ g ts hf _ ss hf.1.2 hf.2.1.2 hf.2.2.1 a b ha (hp.mem_iff.mpr hb) .weak
  | select P f base types extras υ request result target happ =>
      have hall := FiniteQueryPrimitivesProof.everySelectAttemptClosure Symbol arity _ _ _ _ f base types extras υ request hc hf.1 hf.2.1 hf.2.2.1
      obtain ⟨hk,hp,ha⟩ := hall.2.2.2.2.2.2.2.2.2 result happ
      exact ⟨hk,hp,ha,hf.2.2.2⟩
  | fresh P f base types extras α β body i hi =>
      obtain ⟨ordinary,hbody,hfresh,hopened⟩ := freshOpeningAvailability Symbol arity Γ σ τ s t .weak P _ α β body hf
      obtain ⟨hk,hp,ha⟩ := openBounds _ _ _ hc f α β base types extras hf.1 hf.2.1 hf.2.2.1
      exact ⟨hk,hp,ha,ordinary,hbody,hopened i hi⟩
  | copy P f g base types extras ts p he hp => exact retypedFrame s t P f g base types extras ts hf p hp
  | statSide P f g base types extras ts p he hp => exact retypedFrame s t P f g base types extras ts hf p hp
  | statRetained P f g base types extras ts kept retained removed inserted a b he hp hq hn hmem =>
      obtain ⟨ha,hb⟩ := zipMembers hmem
      exact argumentFrame s t P _ g ts hf _ base hf.1.2.1 hf.2.1.2.1 hf.2.2.1.1 a b
        (hp.mem_iff.mpr (List.mem_append.mpr (Or.inl ha))) (hq.mem_iff.mpr (List.mem_append.mpr (Or.inl hb))) .weak
  | statReplaced P f g base types extras ts kept retained removed inserted a b he hp hq hn ha hb =>
      exact argumentFrame s t P _ g ts hf _ base hf.1.2.1 hf.2.1.2.1 hf.2.2.1.1 a b
        (hp.mem_iff.mpr (List.mem_append.mpr (Or.inr ha))) (hq.mem_iff.mpr (List.mem_append.mpr (Or.inr hb))) .strict

end LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphFrameProof
