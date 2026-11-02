module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLattice
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets

deriving instance DecidableEq for Head

def headList {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : List (Head Symbol) :=
  FiniteQueryPrimitives.markedHeads (embed I.source)
abbrev HeadIndex {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) :=
  {f : Head Symbol // f ∈ headList I}
instance headIndexFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Fintype (HeadIndex I) :=
  Fintype.ofFinset (headList I).toFinset (by intro f; exact List.mem_toFinset)

abbrev BaseTuple {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (f : HeadIndex I) (P : World I) :=
  (i : Fin (headArguments arity f.val).length) → Value I ((headArguments arity f.val).get i) P
abbrev Inputs {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (f : HeadIndex I) (P : World I) := BaseTuple I f P × Extras I P

/-- Literal full base tuple and typed extra downset restriction. -/
def inputFamily {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (f : HeadIndex I) : Family I where
  carrier := Inputs I f
  finite := fun P => by
    change Fintype (BaseTuple I f P × Extras I P)
    infer_instance
  equality := fun P a b =>
    decidable_of_iff (a ≤ b ∧ b ≤ a)
      ⟨fun h => le_antisymm h.1 h.2,fun h => by cases h; exact ⟨le_rfl,le_rfl⟩⟩
  order := fun P => inferInstance
  orderDecision := fun P a b => inferInstanceAs (Decidable ((∀ i,a.1 i ≤ b.1 i) ∧ a.2 ≤ b.2))
  restrict := fun {P Q} h a =>
    ⟨fun i => RecursiveNaturalDomains.weaken h (a.1 i),(TypedExtraDownsetsProof.extrasFamily I).restrict h a.2⟩
  restrictIdentity := by
    intro P a
    apply Prod.ext
    · funext i; exact (family I _).restrictIdentity P (a.1 i)
    · exact (TypedExtraDownsetsProof.extrasFamily I).restrictIdentity P a.2
  restrictComposition := by
    intro P Q R h k a
    apply Prod.ext
    · funext i; exact (family I _).restrictComposition P Q R h k (a.1 i)
    · exact (TypedExtraDownsetsProof.extrasFamily I).restrictComposition P Q R h k a.2
  restrictMonotone := by
    intro P Q h a b hab
    constructor
    · intro i; exact (family I _).restrictMonotone P Q h (a.1 i) (b.1 i) (hab.1 i)
    · exact (TypedExtraDownsetsProof.extrasFamily I).restrictMonotone P Q h a.2 b.2 hab.2

instance inputsFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (f : HeadIndex I) (P : World I) : Fintype (Inputs I f P) := (inputFamily I f).finite P
instance inputsEquality {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (f : HeadIndex I) (P : World I) : DecidableEq (Inputs I f P) := (inputFamily I f).equality P
instance inputsOrderDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {f : HeadIndex I} {P : World I} (a b : Inputs I f P) : Decidable (a ≤ b) :=
  (inputFamily I f).orderDecision P a b

abbrev Raw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) :=
  (f : HeadIndex I) → (τ : TypeIndex I) → (P : World I) → Inputs I f P → Value I τ.val P
instance rawFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Fintype (Raw I) :=
  inferInstanceAs (Fintype ((f : HeadIndex I) → (τ : TypeIndex I) → (P : World I) → Inputs I f P → Value I τ.val P))

def Good {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} (M : Raw I) : Prop :=
  (∀ f τ P (a b : Inputs I f P),a ≤ b → M f τ P a ≤ M f τ P b) ∧
  (∀ f τ P Q (h : Extends P Q) (a : Inputs I f P),
    RecursiveNaturalDomains.weaken h (M f τ P a)=M f τ Q ((inputFamily I f).restrict h a))
instance goodDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} (M : Raw I) : Decidable (Good M) :=
  inferInstanceAs (Decidable ((∀ f τ P (a b : Inputs I f P),a ≤ b → M f τ P a ≤ M f τ P b) ∧
  (∀ f τ P Q (h : Extends P Q) (a : Inputs I f P),
    RecursiveNaturalDomains.weaken h (M f τ P a)=M f τ Q ((inputFamily I f).restrict h a))))

abbrev Constructors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) := {M : Raw I // Good M}
instance constructorsFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Fintype (Constructors I) :=
  Fintype.ofFinset (Finset.univ.filter fun M : Raw I => Good M)
    (by intro M; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl)
def enumerateConstructors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Finset (Constructors I) := Finset.univ

def constructorOrder {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : PartialOrder (Constructors I) := inferInstance

noncomputable def supRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (S : Set (Constructors I)) : Raw I :=
  fun f τ P a => (RecursiveNaturalLatticesProof.bounds I τ.val).sup P ((fun M : Constructors I => M.val f τ P a) '' S)
noncomputable def infRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (S : Set (Constructors I)) : Raw I :=
  fun f τ P a => (RecursiveNaturalLatticesProof.bounds I τ.val).inf P ((fun M : Constructors I => M.val f τ P a) '' S)

end LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLattice
