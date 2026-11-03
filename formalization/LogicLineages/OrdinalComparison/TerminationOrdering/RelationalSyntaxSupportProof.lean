module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains
open TypedValueEnvironment CoherentConstructorLattice ConstructorInputLogicalRelation ConfinedStructuralInterpretation
open OriginalSpineActions OrdinaryFunctionalValue FunctionalSpineActions FullListValueApplication RelatedEnvironments ActualValueLogicalRelation
open SourceConstructorIteration ActualComparisonCompleteness TypedObservationAccess RecursiveComparison RelationalSyntax

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem argumentAtSubstitute {Gamma Delta types : List Ty} (args : Arguments Symbol arity Gamma types)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (i : Fin types.length) :
    argumentAt (substituteArguments args s) i=substituteTerm (argumentAt args i) s := by
  induction types with
  | nil => exact Fin.elim0 i
  | cons tau types ih =>
    cases args with
    | cons a rest =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih rest j

theorem currentBits (above : Symbol → Symbol → Prop) {P : World I} {sigma : Ty}
    (a : Value I sigma P) (q : SyntaxAt I sigma P) (ha : Related I above sigma P a q)
    (o : ObservationAt I sigma P) :
    (readBit false a o.val=true → Weak Symbol arity above (portTypes P.val++I.context)
      ⟨sigma,q⟩ ⟨sigma,observedTerm o⟩) ∧
    (readBit true a o.val=true → Strict Symbol arity above (portTypes P.val++I.context)
      ⟨sigma,q⟩ ⟨sigma,observedTerm o⟩) := by
  have H := ActualValueLogicalRelationProof.bitClause Symbol inferInstance arity I above sigma P a q ha
    P (fun _ hp => hp) o
  rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inferInstance arity I sigma P a,
    RelatedOccurrenceMatchingProof.syntaxIdentity] at H
  exact H

theorem currentTuple (above : Symbol → Symbol → Prop) {P : World I} {sigma : Ty}
    (a : Value I sigma P) (q : SyntaxAt I sigma P) (ha : Related I above sigma P a q)
    (types : List Ty) (tau : Ty) (values : Values I types P)
    (args : Arguments Symbol arity (portTypes P.val++I.context) types) (h : sigma=arrows types tau)
    (hn : types≠[]) (hargs : ∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) :
    match applyOriginalWith q (fun v => .var v) args h with
    | none => FullListValueApplication.applyWith a types tau values h=ExecutableDomainBottom.bottomValue I tau P
    | some result => Related I above tau P (FullListValueApplication.applyWith a types tau values h) result := by
  cases h
  let suffix : Suffix (arrows types tau) := fullSuffix types tau hn
  have H := ActualValueLogicalRelationProof.fullTupleClause Symbol inferInstance arity I above
    (arrows types tau) P a q ha P (fun _ hp => hp) suffix values args hargs
  rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inferInstance arity I _ P a,
    RelatedOccurrenceMatchingProof.syntaxIdentity] at H
  have hv : FullListValueApplication.applyWith a types tau values rfl=applyValue a suffix values := by
    change applyFull types tau a values=applyValue a suffix values
    exact FullListValueApplicationProof.nonemptyCalibration Symbol inferInstance arity I types tau P hn a values
  rw [hv]
  dsimp only [suffix,fullSuffix] at H
  cases hx : applyOriginalWith q (fun v => .var v) args rfl with
  | none =>
    simp only [hx] at H ⊢
    exact H
  | some result =>
    simp only [hx] at H ⊢
    exact H

theorem inputFromTuples (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I)
    (b : BaseTuple I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (ht : ∀ tau ∈ types,tau ∈ TypedExtraDownsets.types I)
    (values : Values I types P) (args : Arguments Symbol arity (portTypes P.val++I.context) types)
    (hb : ∀ i,Related I above ((headArguments arity f.val).get i) P (b i) (argumentAt base i))
    (hv : ∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) :
    InputRelated I above f P
      ⟨b,TypedExtraAppendProof.appendExtras (emptyExtras I P) (packArguments types ht values)⟩
      base args := by
  exact ConstructorInputLogicalRelationProof.inputAppend Symbol inferInstance arity I above f P
    ⟨b,emptyExtras I P⟩ base [] .nil types ht values args
    (OrdinaryLogicalRelationProof.emptyInput above f P b base hb) hv

theorem emptyScanner (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma : Ty} (q : ConfinedTerm I Gamma sigma)
    (he : EvaluationRelated I above M q) (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (mask : Protected Gamma) (hr : EnvironmentRelated I above P rho s) (values : Values I [] P) :
    Related I above sigma P (scan q M P rho mask [] sigma values rfl) (substituteTerm q.val s) := by
  rw [ConfinedStructuralInterpretationProof.emptyScanner Symbol inferInstance arity I Gamma sigma q M P rho mask values]
  exact he P rho s hr

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxSupportProof
