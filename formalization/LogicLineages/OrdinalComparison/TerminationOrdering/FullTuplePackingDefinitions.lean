module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePacking
open Source Source.SourceTypeSupport FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets TypedExtraAppend

theorem sourceTypeClosed {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity)
    {τ υ : Ty} (hτ : τ ∈ types I) (hυ : υ ∈ τ.subtypes) : υ ∈ types I := by
  rcases Finset.mem_union.mp hτ with hs | ht
  · exact Finset.mem_union_left _ (Source.SourceTypeSupportProof.subtypeClosedSupport Symbol arity I.context I.sourceType I.source τ hs υ hυ)
  · exact Finset.mem_union_right _ (Source.SourceTypeSupportProof.subtypeClosedSupport Symbol arity I.context I.targetType I.target τ ht υ hυ)

def argumentTag {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity)
    (τ : TypeIndex I) (s : Suffix τ.val) (i : Fin s.val.1.length) : TypeIndex I :=
  ⟨argumentType s i,sourceTypeClosed I τ.property
    ((Source.SourceArrowSuffixesProof.arrowSuffixSubtypes τ.val s.val.1 s.val.2 s.property).2 _ (List.get_mem _ _))⟩

def resultTag {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity)
    (τ : TypeIndex I) (s : Suffix τ.val) : TypeIndex I :=
  ⟨s.val.2,sourceTypeClosed I τ.property
    (Source.SourceArrowSuffixesProof.arrowSuffixSubtypes τ.val s.val.1 s.val.2 s.property).1⟩

/-- Every supplied argument, in its original position, including duplicate entries. -/
def packTuple {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (τ : TypeIndex I) (s : Suffix τ.val) {P : World I} (v : FullTuple I τ.val s P) : List (Packed I P) :=
  List.ofFn fun i => ⟨argumentTag I τ s i,v i⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePacking
