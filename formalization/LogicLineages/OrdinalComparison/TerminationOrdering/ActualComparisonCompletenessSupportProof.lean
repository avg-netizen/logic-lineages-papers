module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness RenamingEquivariance FunctionalSpineActions

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

abbrev Obs (I : Input Symbol arity) := Observation Symbol arity I.context (budget I)

def decode {P : World I} (o : Obs I) (hp : o.ports=P.val) : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context) :=
  ⟨o.resultType,embed (MarkedFAbsTest.bodyAtWorld P o hp)⟩

def Meaning (above : Symbol → Symbol → Prop) [DecidableRel above] (strict : Bool) {Γ : List Ty}
    (s t : RecursiveComparison.Packed Symbol arity Γ) : Prop :=
  ∀ (P : World I) (r : Renaming Γ (portTypes P.val++I.context)) (hs : Confined I s.2)
    (o : Obs I) (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val),
    renamePacked r t=decode o hp →
    readBit strict (interpret ⟨s.2,hs⟩ (limit I above) P (reindex r (identity I P))) o=true

def sourceValue {Γ : List Ty} (p : RecursiveComparison.Packed Symbol arity Γ) (hp : Confined I p.2)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : TypedExtraDownsets.Packed I P :=
  ⟨⟨p.1,FiniteQueryPrimitivesSupportProof.rootType p.2 hp.1⟩,interpret ⟨p.2,hp⟩ M P ρ⟩

def SourceMatch {Γ : List Ty} (M : Constructors I) (P : World I) (ρ : Environment I Γ P)
    (p : RecursiveComparison.Packed Symbol arity Γ) (v : TypedExtraDownsets.Packed I P) : Prop :=
  ∃ hp : Confined I p.2,v=sourceValue p hp M P ρ

def TargetMatch {Γ : List Ty} (P : World I) (r : Renaming Γ (portTypes P.val++I.context))
    (t : RecursiveComparison.Packed Symbol arity Γ) (o : Obs I) : Prop :=
  ∃ (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val),renamePacked r t=decode o hp

def MultiMeaning (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (ss ts : List (RecursiveComparison.Packed Symbol arity Γ)) : Prop :=
  ∃ kept removed retained inserted,ss.Perm (kept++removed) ∧ ts.Perm (retained++inserted) ∧ removed≠[] ∧
    List.Forall₂ (Meaning (I := I) above false) kept retained ∧
    ∀ t ∈ inserted,∃ s ∈ removed,Meaning (I := I) above true s t

theorem pairTruth (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} (strict : Bool)
    {s t : RecursiveComparison.Packed Symbol arity Γ} (hm : Meaning (I := I) above strict s t)
    (P : World I) (r : Renaming Γ (portTypes P.val++I.context))
    {v : TypedExtraDownsets.Packed I P} {o : Obs I}
    (hv : SourceMatch (limit I above) P (reindex r (identity I P)) s v) (ho : TargetMatch P r t o) :
    FiniteOccurrenceMatching.pairBit strict v o=true := by
  rcases hv with ⟨hs,rfl⟩
  rcases ho with ⟨hmembership,hports,he⟩
  exact hm P r hs o hmembership hports he

theorem argumentsMatch {Γ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    List.Forall₂ (SourceMatch M P ρ) (argumentList args) (InterpretedArgumentAppend.packedValues args ha M P ρ) := by
  induction types with
  | nil => cases args; exact .nil
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      rw [InterpretedArgumentAppendProof.packedCons]
      exact .cons ⟨⟨ha.1.1,ha.2.1⟩,rfl⟩ (ih rest ⟨ha.1.2,ha.2.2⟩)

theorem argumentsConfinedMember {Γ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (p : RecursiveComparison.Packed Symbol arity Γ) (hp : p ∈ argumentList args) : Confined I p.2 := by
  induction types with
  | nil => cases args; simp [argumentList] at hp
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ha.1.1,ha.2.1⟩
      · exact ih rest ⟨ha.1.2,ha.2.2⟩ hp

theorem leftWitness {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys,R x y := by
  induction h with
  | nil => simp at hx
  | @cons a b xs ys hab h ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b,List.mem_cons_self,hab⟩
    · rcases ih hx with ⟨y,hy,hr⟩
      exact ⟨y,List.mem_cons_of_mem _ hy,hr⟩

theorem rightWitness {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs,R x y := by
  induction h with
  | nil => simp at hy
  | @cons a b xs ys hab h ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a,List.mem_cons_self,hab⟩
    · rcases ih hy with ⟨x,hx,hr⟩
      exact ⟨x,List.mem_cons_of_mem _ hx,hr⟩

theorem splitMatch {α β : Type} {R : α → β → Prop} (xs zs : List α) {ys : List β}
    (h : List.Forall₂ R (xs++zs) ys) : ∃ as bs,ys=as++bs ∧ List.Forall₂ R xs as ∧ List.Forall₂ R zs bs := by
  induction xs generalizing ys with
  | nil => exact ⟨[],ys,rfl,.nil,h⟩
  | cons x xs ih =>
    cases h with
    | cons hxy hrest =>
      rcases ih hrest with ⟨as,bs,rfl,ha,hb⟩
      exact ⟨_,bs,rfl,.cons hxy ha,hb⟩

theorem targetTyped {P : World I} {τ : Ty} (o : ObservationAt I τ P) :
    decode o.val o.property.2.1=⟨τ,observedTerm o⟩ := by
  rcases o with ⟨⟨ports,σ,body⟩,ho,hp,ht⟩
  dsimp at hp ht
  subst ports
  subst σ
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSupportProof
