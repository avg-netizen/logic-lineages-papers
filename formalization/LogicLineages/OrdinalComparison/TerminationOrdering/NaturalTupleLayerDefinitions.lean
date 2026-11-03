module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsProof
public import LogicLineages.OrdinalComparison.SourceArrowSuffixesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayer
open Source Source.SourceArrowSuffixes Source.SourceSpecialApplication FiniteObservationBits

/-- Computational ordered family data. Completeness is deliberately not a field. -/
structure Family {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) where
  carrier : World I → Type
  finite : ∀ P,Fintype (carrier P)
  equality : ∀ P,DecidableEq (carrier P)
  order : ∀ P,PartialOrder (carrier P)
  orderDecision : ∀ P,DecidableRel (fun a b : carrier P => (order P).le a b)
  restrict : ∀ {P Q : World I},Extends P Q → carrier P → carrier Q
  restrictIdentity : ∀ P (a : carrier P),restrict (fun _ hp => hp) a=a
  restrictComposition : ∀ P Q R (h : Extends P Q) (k : Extends Q R) (a : carrier P),
    restrict k (restrict h a)=restrict (fun p hp => k p (h p hp)) a
  restrictMonotone : ∀ P Q (h : Extends P Q) (a b : carrier P),
    (order P).le a b → (order Q).le (restrict h a) (restrict h b)

instance familyFinite {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {D : Family I} {P : World I} :
    Fintype (D.carrier P) := D.finite P
instance familyEquality {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {D : Family I} {P : World I} :
    DecidableEq (D.carrier P) := D.equality P
instance familyOrder {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {D : Family I} {P : World I} :
    PartialOrder (D.carrier P) := D.order P
instance familyOrderDecision {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {D : Family I} {P : World I} :
    DecidableRel (fun a b : D.carrier P => a ≤ b) := D.orderDecision P

abbrev Lower {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) :=
  (υ : Ty) → typeSize υ < typeSize τ → Family I

abbrev Suffix (τ : Ty) := {p : List Ty × Ty // p ∈ arrowSuffixes τ}
instance suffixFinite (τ : Ty) : Fintype (Suffix τ) :=
  Fintype.ofFinset (arrowSuffixes τ).toFinset (by intro p; exact List.mem_toFinset)

def argumentType {τ : Ty} (s : Suffix τ) (i : Fin s.val.1.length) : Ty := s.val.1.get i

def argumentFamily {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    (D : Lower I τ) (s : Suffix τ) (i : Fin s.val.1.length) : Family I :=
  D (argumentType s i) ((Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ s.val.1 s.val.2 s.property).2 _ (List.get_mem _ _))

def resultFamily {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    (D : Lower I τ) (s : Suffix τ) : Family I :=
  D s.val.2 (Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ s.val.1 s.val.2 s.property).1

abbrev Tuple {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    (D : Lower I τ) (s : Suffix τ) (P : World I) :=
  (i : Fin s.val.1.length) → (argumentFamily D s i).carrier P

instance tupleOrderDecision {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {s : Suffix τ} {P : World I} (v w : Tuple D s P) : Decidable (v ≤ w) :=
  inferInstanceAs (Decidable (∀ i,v i ≤ w i))

def tupleWeaken {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {s : Suffix τ} {P Q : World I} (h : Extends P Q) (v : Tuple D s P) : Tuple D s Q :=
  fun i => (argumentFamily D s i).restrict h (v i)

/-- Every actual nonempty suffix has one table consuming its entire ordered tuple. -/
abbrev Raw {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty)
    (D : Lower I τ) (P : World I) :=
  Bits I τ P × ((Q : Future P) → (s : Suffix τ) → Tuple D s Q.val → (resultFamily D s).carrier Q.val)

instance rawFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P : World I) : Fintype (Raw I τ D P) :=
  inferInstanceAs (Fintype (Bits I τ P × ((Q : Future P) → (s : Suffix τ) → Tuple D s Q.val → (resultFamily D s).carrier Q.val)))

def Good {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {P : World I} (a : Raw I τ D P) : Prop :=
  (∀ (Q : Future P) (s : Suffix τ) (v w : Tuple D s Q.val),v ≤ w → a.2 Q s v ≤ a.2 Q s w) ∧
  (∀ (Q R : Future P) (h : Extends Q.val R.val) (s : Suffix τ) (v : Tuple D s Q.val),
    (resultFamily D s).restrict h (a.2 Q s v)=a.2 R s (tupleWeaken h v))

instance goodDecision {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {P : World I} (a : Raw I τ D P) : Decidable (Good a) :=
  inferInstanceAs (Decidable ((∀ (Q : Future P) (s : Suffix τ) (v w : Tuple D s Q.val),v ≤ w → a.2 Q s v ≤ a.2 Q s w) ∧
  (∀ (Q R : Future P) (h : Extends Q.val R.val) (s : Suffix τ) (v : Tuple D s Q.val),
    (resultFamily D s).restrict h (a.2 Q s v)=a.2 R s (tupleWeaken h v))))

abbrev Natural {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty)
    (D : Lower I τ) (P : World I) := {a : Raw I τ D P // Good a}

instance naturalFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P : World I) : Fintype (Natural I τ D P) :=
  Fintype.ofFinset (Finset.univ.filter fun a : Raw I τ D P => Good a)
    (by intro a; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl)

def enumerateNatural {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P : World I) : Finset (Natural I τ D P) := Finset.univ

def rawWeaken {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {P Q : World I} (h : Extends P Q) (a : Raw I τ D P) : Raw I τ D Q :=
  ⟨FiniteObservationBits.weaken h a.1,fun R s v => a.2 ⟨R.val,fun p hp => R.property p (h p hp)⟩ s v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayer
