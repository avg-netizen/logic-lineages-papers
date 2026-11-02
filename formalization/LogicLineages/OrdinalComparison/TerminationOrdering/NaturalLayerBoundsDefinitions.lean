module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBounds
open Source Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer

/-- Mathematical bounds in the family's existing order, separate from executable family data. -/
structure Bounds {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (D : Family I) where
  sup : ∀ P,Set (D.carrier P) → D.carrier P
  inf : ∀ P,Set (D.carrier P) → D.carrier P
  supSpec : ∀ P S,IsLUB S (sup P S)
  infSpec : ∀ P S,IsGLB S (inf P S)
  supRestriction : ∀ P Q (h : Extends P Q) S,D.restrict h (sup P S)=sup Q (D.restrict h '' S)
  infRestriction : ∀ P Q (h : Extends P Q) S,D.restrict h (inf P S)=inf Q (D.restrict h '' S)

abbrev LowerBounds {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    (D : Lower I τ) := (υ : Ty) → (h : typeSize υ < typeSize τ) → Bounds (D υ h)

def resultBounds {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} (L : LowerBounds D) (s : Suffix τ) : Bounds (resultFamily D s) :=
  L s.val.2 (Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ s.val.1 s.val.2 s.property).1

noncomputable def supRaw {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)) : Raw I τ D P :=
  ⟨sSup ((fun a : Natural I τ D P => a.val.1) '' S),
    fun Q s v => (resultBounds L s).sup Q.val ((fun a : Natural I τ D P => a.val.2 Q s v) '' S)⟩

noncomputable def infRaw {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)) : Raw I τ D P :=
  ⟨sInf ((fun a : Natural I τ D P => a.val.1) '' S),
    fun Q s v => (resultBounds L s).inf Q.val ((fun a : Natural I τ D P => a.val.2 Q s v) '' S)⟩

def naturalWeaken {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {D : Lower I τ} {P Q : World I} (h : Extends P Q) (a : Natural I τ D P) : Natural I τ D Q :=
  ⟨rawWeaken h a.val,NaturalTupleLayerProof.naturalPreservation Symbol arity I τ D P Q h a.val a.property⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBounds
