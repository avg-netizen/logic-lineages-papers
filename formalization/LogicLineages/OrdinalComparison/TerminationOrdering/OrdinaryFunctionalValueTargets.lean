module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice OrdinaryObservationView FiniteOccurrenceMatching TypedObservationAccess OrdinaryFunctionalValue

def SourceHeadResultTypes : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I),headResult f.val ∈ types I

def BasePackingCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P), (packBase f b).length=(headArguments arity f.val).length ∧ ∀ i : Fin (headArguments arity f.val).length,(packBase f b)[i.val]?=some ⟨baseTag I f i,b i⟩

def FunCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P) (o : Observation Symbol arity I.context (budget I)), funMatch f b o=true ↔ ∃ (g : Head Symbol) (args : Arguments Symbol arity (portTypes o.ports++I.context) (headArguments arity g)), rootView o.body=some ⟨g,args⟩ ∧ RecursiveComparison.headEquivalent f.val g ∧ headResult f.val=headResult g ∧ ∃ matched,(plainChildren o).Perm matched ∧ List.Forall₂ (fun p t => pairBit false p t=true) (packBase f b) matched

def OrdinaryBitEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P), ∃ hr : headResult f.val ∈ types I,∀ Q : Future P, ((layerView I (headResult f.val) P (ordinaryValue M f b)).val.1 Q).1=true ∧ ∀ o : ObservationAt I (headResult f.val) Q.val, let marked := M.val f ⟨headResult f.val,hr⟩ Q.val ⟨weakenBase Q.property b,emptyExtras I Q.val⟩; ((layerView I (headResult f.val) P (ordinaryValue M f b)).val.1 Q).2.1 o=(funMatch f (weakenBase Q.property b) o.val || readBit false marked o.val) ∧ ((layerView I (headResult f.val) P (ordinaryValue M f b)).val.1 Q).2.2 o=readBit false marked o.val

def FullTupleEquation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P), ∃ hr : headResult f.val ∈ types I,∀ (Q : Future P) (s : Suffix (headResult f.val)) (v : FullTuple I (headResult f.val) s Q.val), (layerView I (headResult f.val) P (ordinaryValue M f b)).val.2 Q s v=M.val f (FullTuplePacking.resultTag I ⟨headResult f.val,hr⟩ s) Q.val ⟨weakenBase Q.property b,TypedExtraAppendProof.appendExtras (emptyExtras I Q.val) (FullTuplePacking.packTuple ⟨headResult f.val,hr⟩ s v)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueTargets
