module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxFunctionalProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains
open TypedValueEnvironment TypedExtraDownsets CoherentConstructorLattice ConstructorInputLogicalRelation ConfinedStructuralInterpretation
open OriginalSpineActions FunctionalSpineActions FullListValueApplication FullTuplePacking OrdinaryFunctionalValue
open RelatedEnvironments ActualValueLogicalRelation RelationalSyntax RelationalSyntaxSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem appendedFamily (above : Symbol → Symbol → Prop) (M : Constructors I) (hM : FamilySound I above M)
    (f : HeadIndex I) (sigma : TypeIndex I) (P : World I) (state : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (oldTypes : List Ty) (oldArgs : Arguments Symbol arity (portTypes P.val++I.context) oldTypes)
    (hi : InputRelated I above f P state base oldArgs)
    (types : List Ty) (tau : Ty) (values : Values I types P)
    (args : Arguments Symbol arity (portTypes P.val++I.context) types) (h : sigma.val=arrows types tau)
    (hn : types≠[]) (hv : ∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) :
    Related I above tau P
      (M.val f (resultTag I sigma (sourceSuffix sigma types tau h hn)) P
        (FunctionalTupleBuilder.appendInput state (packTuple sigma (sourceSuffix sigma types tau h hn) values)))
      (.marked f.val tau base (oldTypes++types) (appendArguments oldArgs args)) := by
  let suffix := sourceSuffix sigma types tau h hn
  have ht : ∀ upsilon ∈ types,upsilon ∈ TypedExtraDownsets.types I := fun upsilon hu =>
    sourceTypeClosed I sigma.property ((Source.SourceArrowSuffixesProof.arrowSuffixSubtypes sigma.val _ _ suffix.property).2 upsilon hu)
  have hin := ConstructorInputLogicalRelationProof.inputAppend Symbol inferInstance arity I above f P state
    base oldTypes oldArgs types ht values args hi hv
  exact hM f (resultTag I sigma suffix) P
    (FunctionalTupleBuilder.appendInput state (packTuple sigma suffix values)) base (oldTypes++types)
    (appendArguments oldArgs args) hin

theorem ordinaryCase (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (hM : FamilySound I above M)
    {Gamma : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (hb : ArgumentsConfined I base) (hq : Confined I (.ordinary f base))
    (hbase : ArgumentsRelated I above M base hb) :
    EvaluationRelated I above M ⟨.ordinary f base,hq⟩ ∧ ScannerRelated I above M ⟨.ordinary f base,hq⟩ := by
  let fI : HeadIndex I := ⟨f,hq.2.1⟩
  have he : EvaluationRelated I above M ⟨.ordinary f base,hq⟩ := by
    intro P rho s hr
    change Related I above (headResult f) P
      (ordinaryValue M fI (ActualOriginalApplication.argumentValues base hb M P rho))
      (.ordinary f (substituteArguments base s))
    exact OrdinaryLogicalRelationProof.ordinaryRelated Symbol inferInstance arity I above inferInstance M fI P
      _ _ hM (hbase P rho s hr)
  refine ⟨he,?_⟩
  intro P rho s mask hr types tau values args h hargs
  cases args with
  | nil =>
    cases h
    change Related I above (headResult f) P
      (scan ⟨.ordinary f base,hq⟩ M P rho mask [] (headResult f) values rfl)
      (substituteTerm (.ordinary f base) s)
    exact emptyScanner above M ⟨.ordinary f base,hq⟩ he P rho s mask hr values
  | cons a rest =>
    let sigma : TypeIndex I := ⟨headResult f,
      OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inferInstance arity I fI⟩
    have hi := OrdinaryLogicalRelationProof.emptyInput above fI P
      (ActualOriginalApplication.argumentValues base hb M P rho) (substituteArguments base s) (hbase P rho s hr)
    have H := appendedFamily above M hM fI sigma P
      ⟨ActualOriginalApplication.argumentValues base hb M P rho,emptyExtras I P⟩
      (substituteArguments base s) [] .nil hi _ tau values (.cons a rest) h (by simp) hargs
    simp only [ProtectedApply.applyWith,applyOriginalWith,substituteTerm]
    change Related I above tau P (ordinaryScan fI (buildArguments I base hb) M P rho mask _ tau values h) _
    simp only [ordinaryScan,functionalScan,dif_neg (List.cons_ne_nil _ _)]
    exact H

theorem markedCase (above : Symbol → Symbol → Prop) (M : Constructors I) (hM : FamilySound I above M)
    {Gamma : List Ty} (f : Head Symbol) (out : Ty)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Gamma extraTypes)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras)
    (hq : Confined I (.marked f out base extraTypes extras))
    (hbase : ArgumentsRelated I above M base hb) (hextra : ArgumentsRelated I above M extras hx) :
    EvaluationRelated I above M ⟨.marked f out base extraTypes extras,hq⟩ ∧
      ScannerRelated I above M ⟨.marked f out base extraTypes extras,hq⟩ := by
  let fI : HeadIndex I := ⟨f,hq.2.1⟩
  let sigma : TypeIndex I := ⟨out,hq.1.1⟩
  have hinput (P : World I) (rho : Environment I Gamma P)
      (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
      (hr : EnvironmentRelated I above P rho s) :
      InputRelated I above fI P (markedState fI (buildArguments I base hb) extraTypes
        (argumentTypeList extras hx) (buildArguments I extras hx) M P rho)
        (substituteArguments base s) (substituteArguments extras s) :=
    inputFromTuples above fI P _ _ extraTypes (argumentTypeList extras hx) _ _
      (hbase P rho s hr) (hextra P rho s hr)
  have he : EvaluationRelated I above M ⟨.marked f out base extraTypes extras,hq⟩ := by
    intro P rho s hr
    exact hM fI sigma P _ (substituteArguments base s) extraTypes (substituteArguments extras s) (hinput P rho s hr)
  refine ⟨he,?_⟩
  intro P rho s mask hr types tau values args h hargs
  cases args with
  | nil =>
    cases h
    change Related I above tau P
      (scan ⟨.marked f tau base extraTypes extras,hq⟩ M P rho mask [] tau values rfl)
      (substituteTerm (.marked f tau base extraTypes extras) s)
    exact emptyScanner above M ⟨.marked f _ base extraTypes extras,hq⟩ he P rho s mask hr values
  | cons a rest =>
    have H := appendedFamily above M hM fI sigma P
      (markedState fI (buildArguments I base hb) extraTypes (argumentTypeList extras hx)
        (buildArguments I extras hx) M P rho)
      (substituteArguments base s) extraTypes (substituteArguments extras s) (hinput P rho s hr)
      _ tau values (.cons a rest) h (by simp) hargs
    simp only [ProtectedApply.applyWith,applyOriginalWith,substituteTerm]
    change Related I above tau P
      (markedScan fI sigma (buildArguments I base hb) extraTypes (argumentTypeList extras hx)
        (buildArguments I extras hx) M P rho mask _ tau values h) _
    simp only [markedScan,functionalScan,dif_neg (List.cons_ne_nil _ _)]
    exact H

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxFunctionalProof
