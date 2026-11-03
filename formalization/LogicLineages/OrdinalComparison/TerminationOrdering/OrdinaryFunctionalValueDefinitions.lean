module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValue
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice OrdinaryObservationView FiniteOccurrenceMatching TypedObservationAccess

deriving instance DecidableEq for RecursiveComparison.HeadClass

instance equivalentDecision {Symbol : Type} [DecidableEq Symbol] (f g : Head Symbol) : Decidable (RecursiveComparison.headEquivalent f g) :=
  inferInstanceAs (Decidable (RecursiveComparison.headClass f=RecursiveComparison.headClass g))

def emptyExtras {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I) : Extras I P :=
  fun _ => ⟨∅,by intro a ha; exact False.elim (Finset.notMem_empty a ha)⟩

def baseTag {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (f : HeadIndex I) (i : Fin (headArguments arity f.val).length) : TypeIndex I :=
  ⟨(headArguments arity f.val).get i,CoherentConstructorLatticeProof.headBaseTypes Symbol inferInstance arity I f _ (List.get_mem _ _)⟩

def packBase {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} (b : BaseTuple I f P) : List (Packed I P) :=
  List.ofFn fun i => ⟨baseTag I f i,b i⟩

def weakenBase {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {f : HeadIndex I} {P Q : World I} (h : Extends P Q) (b : BaseTuple I f P) : BaseTuple I f Q :=
  fun i => RecursiveNaturalDomains.weaken h (b i)

def funMatch {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} (b : BaseTuple I f P) (o : Observation Symbol arity I.context (budget I)) : Bool :=
  match rootView o.body with
  | none => false
  | some ⟨g,_⟩ => decide (RecursiveComparison.headEquivalent f.val g) && decide (headResult f.val=headResult g) &&
      weakTest (pairBit false) (packBase f b) (plainChildren o)

def ordinaryBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (hr : headResult f.val ∈ types I) {P : World I}
    (b : BaseTuple I f P) : Bits I (headResult f.val) P := fun Q =>
  let bQ := weakenBase Q.property b
  let marked := M.val f ⟨headResult f.val,hr⟩ Q.val ⟨bQ,emptyExtras I Q.val⟩
  ⟨true,(fun o => funMatch f bQ o.val || readBit false marked o.val),(fun o => readBit false marked o.val)⟩

/-- The source head result guard is discharged by an independent original-term occurrence proof. -/
def ordinaryValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (b : BaseTuple I f P) : Value I (headResult f.val) P :=
  if hr : headResult f.val ∈ types I then
    FunctionalTupleBuilderProof.buildValue M f ⟨headResult f.val,hr⟩ (ordinaryBits M f hr b) ⟨b,emptyExtras I P⟩
  else ExecutableDomainBottom.bottomValue I (headResult f.val) P

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValue
