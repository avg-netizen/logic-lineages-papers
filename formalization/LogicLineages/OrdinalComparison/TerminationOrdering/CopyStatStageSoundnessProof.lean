module
public import LogicLineages.OrdinalComparison.TerminationOrdering.CopyStatStageSoundnessTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CopyStatStageSoundnessProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness ActualComparisonCompletenessSupportProof RelatedOccurrenceMatching ActualValueLogicalRelation OrdinaryObservationView OrdinaryFunctionalValue CopyStatStageSoundness

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem renamePackedIdentity {Γ : List Ty} (q : RecursiveComparison.Packed Symbol arity Γ) :
    RenamingEquivariance.renamePacked (fun v => v) q=q := by
  exact congrArg (fun t => (⟨q.1,t⟩ : RecursiveComparison.Packed Symbol arity Γ))
    (Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Γ q.1 q.2)

theorem childrenObserved (P : World I) (g : Head Symbol)
    (args : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity g))
    (o : Obs I) (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val)
    (he : (⟨headResult g,.ordinary g args⟩ : RecursiveComparison.Packed Symbol arity _)=decode o hp) :
    List.Forall₂ (Observed I P) (plainChildren o) (argumentList args) := by
  have H := ActualComparisonCompletenessOrdinaryProof.targetArguments P (fun v => v) g args o ho hp
    ((renamePackedIdentity _).trans he)
  generalize argumentList args=ts at H ⊢
  generalize plainChildren o=os at H ⊢
  induction H with
  | nil => exact .nil
  | cons h ht ih =>
    rcases h with ⟨hom,hp,he⟩
    exact .cons ⟨hom,hp,(renamePackedIdentity _).symm.trans he⟩ ih

theorem childrenWeak (above : Symbol → Symbol → Prop) (M : Constructors I) (hM : FamilySound I above M)
    (f : HeadIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types) (ha : InputRelated I above f P a base extras)
    (os : List (Obs I)) (ts : List (RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context)))
    (ho : List.Forall₂ (Observed I P) os ts)
    (hw : ∀ c ∈ os,∃ ht : c.resultType ∈ TypedExtraDownsets.types I,TypedObservationAccess.readBit false (M.val f ⟨c.resultType,ht⟩ P a) c=true) :
    ∀ t ∈ ts,Weak Symbol arity above (portTypes P.val++I.context) ⟨t.1,.marked f.val t.1 base types extras⟩ t := by
  intro t ht
  obtain ⟨c,hc,hobs⟩ := rightWitness ho ht
  obtain ⟨hct,hbit⟩ := hw c hc
  rcases hobs with ⟨hom,hp,rfl⟩
  exact (RelatedOccurrenceMatchingProof.pairSound Symbol inferInstance arity I above P
    ⟨⟨c.resultType,hct⟩,M.val f ⟨c.resultType,hct⟩ P a⟩ c _ _
    ⟨.marked f.val c.resultType base types extras,rfl,hM f ⟨c.resultType,hct⟩ P a base types extras ha⟩
    ⟨hom,hp,rfl⟩).1 hbit

theorem packedArgumentsRelated (above : Symbol → Symbol → Prop) (P : World I) (types : List Ty)
    (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I) (values : FullListValueApplication.Values I types P)
    (args : Arguments Symbol arity (portTypes P.val++I.context) types)
    (ha : ∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) :
    List.Forall₂ (PackedRelated I above P) (FunctionalSpineActions.packArguments types ht values) (argumentList args) := by
  induction types with
  | nil => cases args; exact .nil
  | cons τ rest ih =>
    cases args with
    | cons q qs =>
      simp only [FunctionalSpineActions.packArguments,List.ofFn_succ,argumentList]
      exact .cons ⟨q,rfl,ha 0⟩ (ih (fun υ hυ => ht υ (List.mem_cons_of_mem _ hυ)) (fun i => values i.succ) qs (fun i => ha i.succ))

theorem copySound : CopyStatStageSoundnessTargets.CopySound := by
  intro Symbol inst arity I above dec M f τ P a base types extras o hM ha hb
  rcases τ with ⟨τ,hτ⟩
  rcases o with ⟨⟨ports,υ,body⟩,hom,hp,ht⟩
  dsimp at hp ht
  subst ports
  subst υ
  obtain ⟨g,args,hroot,habove,hchildren⟩ := (MarkedCopyTestProof.copyCalibration Symbol inst arity I above dec M f P a _).mp hb
  have he := (OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g args).mp hroot
  have ht := congrArg Sigma.fst he
  dsimp at ht
  subst τ
  have H := childrenObserved P g args _ hom rfl he.symm
  have hw := Weak.copy f.val g base types extras args habove (childrenWeak above M hM f P a base types extras ha _ _ H hchildren)
  exact he.symm ▸ hw

theorem statSound : CopyStatStageSoundnessTargets.StatSound := by
  intro Symbol inst arity I above dec M f τ P a base types extras o hM ha hb
  rcases τ with ⟨τ,hτ⟩
  rcases o with ⟨⟨ports,υ,body⟩,hom,hp,ht⟩
  dsimp at hp ht
  subst ports
  subst υ
  obtain ⟨g,args,hroot,hequiv,hstrict,hchildren⟩ := (MarkedStatTestProof.statCalibration Symbol inst arity I M f P a _).mp hb
  have he := (OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g args).mp hroot
  have ht := congrArg Sigma.fst he
  dsimp at ht
  subst τ
  have H := childrenObserved P g args _ hom rfl he.symm
  have hv := packedArgumentsRelated above P (headArguments arity f.val)
    (CoherentConstructorLatticeProof.headBaseTypes Symbol inst arity I f) a.1 base ha.1
  have htest := (FiniteOccurrenceMatchingProof.strictCalibration Symbol inst arity I P (packBase f a.1) (plainChildren ⟨P.val,headResult g,body⟩)).mpr hstrict
  have hm := RelatedOccurrenceMatchingProof.strictSound Symbol inst arity I above P _ _ _ _ hv H htest
  have hw := Weak.stat f.val g base types extras args hequiv hm (childrenWeak above M hM f P a base types extras ha _ _ H hchildren)
  exact he.symm ▸ hw

end LogicLineages.OrdinalComparison.TerminationOrdering.CopyStatStageSoundnessProof
