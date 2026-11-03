module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkSupportProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation RecursiveComparison TypedObservationAccess SourceConstructorIteration ActualStrictMark FunctionalSpineActions OrdinaryFunctionalValue LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem markConfined {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q) (r : MarkedTerm Symbol arity Γ τ),strictMark q=some r → Confined I r := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro hq r he; simp [strictMark] at he
  | lam body ih =>
    intro hq r he
    cases hb : strictMark body with
    | none => simp [strictMark,hb] at he
    | some b =>
      simp only [strictMark,hb,Option.map_some] at he
      cases Option.some.inj he
      have hr := ih ⟨hq.1.2.2,hq.2⟩ b hb
      exact ⟨⟨hq.1.1,hq.1.2.1,hr.1⟩,hr.2⟩
  | ordinary f base ih =>
    intro hq r he
    cases Option.some.inj he
    exact ⟨⟨hq.1.1,hq.1.2,trivial⟩,⟨hq.2.1,hq.2.2,trivial⟩⟩
  | marked f output base ts extras ihb ihe => intro hq r he; simp [strictMark] at he
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem readsEqual {P : World I} {τ : Ty} (a b : Value I τ P)
    (he : ∀ (Q : Future P) (o : ObservationAt I τ Q.val),coordinate true a Q o=coordinate false b Q o)
    (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)) : readBit true a o=readBit false b o := by
  by_cases h : Accepted I τ P o
  · simp only [readBit,dif_pos h,acceptedCoordinate]
    exact he _ _
  · simp only [readBit,dif_neg h]

theorem readFalse {P : World I} {τ : Ty} (a : Value I τ P) (he : StrictEmpty a)
    (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)) : readBit true a o=false := by
  by_cases h : Accepted I τ P o
  · simp only [readBit,dif_pos h,acceptedCoordinate]
    exact he _ _
  · simp only [readBit,dif_neg h]

theorem emptyWeaken {P Q : World I} {τ : Ty} (h : Extends P Q) (a : Value I τ P) (he : StrictEmpty a) :
    StrictEmpty (RecursiveNaturalDomains.weaken h a) := by
  intro R o
  simp only [coordinate,if_true,RecursiveNaturalDomainsProof.layerViewWeaken]
  exact he ⟨R.val,fun p hp => R.property p (h p hp)⟩ o

theorem variableEmpty {P : World I} {τ : Ty} (v : Variable (portTypes P.val++I.context) τ) :
    StrictEmpty (LiteralVariableValueProof.variableValue (I := I) v) := by
  intro Q o
  simp only [coordinate,if_true,LiteralVariableValueProof.variableValue,RecursiveNaturalDomainsProof.layerViewFold]
  rfl

theorem openingEmpty {Γ : List Ty} {P : World I} (ρ : Environment I Γ P) (hρ : VariablesStrictEmpty ρ)
    (σ υ : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P σ υ i) :
    VariablesStrictEmpty (openingEnvironment ρ σ υ i h) := by
  intro τ v
  cases v with
  | here => exact variableEmpty (I := I) (P := ⟨(i,σ)::P.val,h.2.1⟩) (τ := σ) .here
  | there v => exact emptyWeaken _ (ρ v) (hρ v)

theorem emptyAppend {P : World I} : TypedExtraAppendProof.appendExtras (emptyExtras I P) []=emptyExtras I P := by
  funext τ
  apply Subtype.ext
  exact TypedExtraAppendProof.emptyIdentity Symbol inferInstance arity I P (emptyExtras I P) τ

theorem ordinaryReads (M : Constructors I) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P)
    (hr : headResult f.val ∈ TypedExtraDownsets.types I)
    (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)) :
    readBit true (ordinaryValue M f b) o=readBit false (M.val f ⟨headResult f.val,hr⟩ P ⟨b,emptyExtras I P⟩) o := by
  apply readsEqual
  intro Q obs
  obtain ⟨hr',hh⟩ := OrdinaryFunctionalValueProof.ordinaryBitEquations Symbol inferInstance arity I M f P b
  have hi : (inputFamily I f).restrict Q.property ⟨b,emptyExtras I P⟩=⟨weakenBase Q.property b,emptyExtras I Q.val⟩ := by
    apply Prod.ext
    · rfl
    · exact OrdinaryFunctionalValueProof.emptyRestriction Q.property
  have hm := (M.property.2 f ⟨headResult f.val,hr⟩ P Q.val Q.property ⟨b,emptyExtras I P⟩).trans
    (congrArg (M.val f ⟨headResult f.val,hr⟩ Q.val) hi)
  exact ((hh Q).2 obs).2.trans
    ((congrArg (fun a => readBit false a obs.val) hm.symm).trans
      ((TypedObservationAccessProof.restrictionAccess Symbol inferInstance arity I (headResult f.val) P false Q.val Q.property
        (M.val f ⟨headResult f.val,hr⟩ P ⟨b,emptyExtras I P⟩) obs.val (by intro p hp; simpa only [obs.property.2.1] using hp)).trans
        (TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I (headResult f.val) P false _ Q obs)))

theorem markedEmpty (above : Symbol → Symbol → Prop) [DecidableRel above] (f : HeadIndex I)
    (τ : TypedExtraDownsets.TypeIndex I) (P : World I) (a : Inputs I f P) : StrictEmpty ((limit I above).val f τ P a) := by
  intro Q o
  exact ((ActualLimitInterpretationProof.sourceBitEquations Symbol inferInstance arity I above inferInstance f τ P a Q).2 o).2

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkSupportProof
