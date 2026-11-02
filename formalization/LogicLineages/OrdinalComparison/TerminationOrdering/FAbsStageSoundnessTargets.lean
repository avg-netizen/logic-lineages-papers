module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SelectStageSoundnessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness CopyStatStageSoundness

def FAbsSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val)) (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types) (o : ObservationAt I τ.val P),
  FamilySound I above M → InputRelated I above f P a base extras → MarkedFAbsTest.fAbsTest M f a o.val=true →
  Weak Symbol arity above (portTypes P.val++I.context) ⟨τ.val,sourceState f τ P base types extras⟩ ⟨τ.val,observedTerm o⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessTargets
