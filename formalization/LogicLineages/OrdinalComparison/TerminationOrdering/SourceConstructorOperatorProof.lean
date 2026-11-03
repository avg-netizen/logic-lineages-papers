module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorProof
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalTupleBuilder SourceConstructorOperator

theorem valueLayer {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I)
    {P : World I} (a : Inputs I f P) :
    (layerView I τ.val P (markedValue above M f τ a)).val=buildRaw M f τ (markedBits above M f τ a) a := by
  simp only [markedValue,FunctionalTupleBuilderProof.buildValue,RecursiveNaturalDomainsProof.layerViewFold]

theorem sourceBitEquations : SourceConstructorOperatorTargets.SourceBitEquations := by
  intro Symbol inst arity I above dec M f τ P a Q
  simp only [operatorRaw]
  rw [valueLayer]
  exact ⟨rfl,fun _ => ⟨rfl,rfl⟩⟩

theorem fullTupleEquation : SourceConstructorOperatorTargets.FullTupleEquation := by
  intro Symbol inst arity I above dec M f τ P a Q s v
  change (layerView I τ.val P (markedValue above M f τ a)).val.2 Q s v=_
  rw [valueLayer]
  rfl

theorem orMonotone {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) : (a || c) ≤ (b || d) := by
  apply Bool.le_iff_imp.mpr
  intro ht
  rcases Bool.or_eq_true_iff.mp ht with ha | hc
  · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.le_iff_imp.mp hab ha))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.le_iff_imp.mp hcd hc))

theorem bitsMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] {M N : Constructors I} (f : HeadIndex I) (τ : TypeIndex I)
    {P : World I} {a b : Inputs I f P} (hMN : M ≤ N) (hab : a ≤ b) :
    markedBits above M f τ a ≤ markedBits above N f τ b := by
  intro Q
  have hinput := (inputFamily I f).restrictMonotone P Q.val Q.property a b hab
  refine ⟨le_rfl,?_,fun _ => le_rfl⟩
  intro o
  exact orMonotone (orMonotone (orMonotone
    (MarkedSelectTestProof.testMonotone Symbol inferInstance arity I M N f Q.val _ _ o.val hMN hinput)
    (MarkedCopyTestProof.testMonotone Symbol inferInstance arity I above inferInstance M N f Q.val _ _ o.val hMN hinput))
    (MarkedStatTestProof.testMonotone Symbol inferInstance arity I M N f Q.val _ _ o.val hMN hinput))
    (MarkedFAbsTestProof.testMonotone Symbol inferInstance arity I M N f Q.val _ _ o.val hMN hinput)

theorem bitsWeakening {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I)
    {P Q : World I} (h : Extends P Q) (a : Inputs I f P) :
    FiniteObservationBits.weaken h (markedBits above M f τ a)=markedBits above M f τ ((inputFamily I f).restrict h a) := by
  funext R
  simp only [FiniteObservationBits.weaken,markedBits,(inputFamily I f).restrictComposition]

theorem valueMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] {M N : Constructors I} (f : HeadIndex I) (τ : TypeIndex I)
    {P : World I} {a b : Inputs I f P} (hMN : M ≤ N) (hab : a ≤ b) :
    markedValue above M f τ a ≤ markedValue above N f τ b := by
  apply (RecursiveNaturalDomainsProof.transportOrder (family I τ.val)
    (NaturalTupleLayerProof.layerFamily I τ.val (lower I τ.val)) (familyEquation I τ.val) P _ _).mpr
  change (layerView I τ.val P (markedValue above M f τ a)).val ≤ (layerView I τ.val P (markedValue above N f τ b)).val
  rw [valueLayer,valueLayer]
  exact FunctionalTupleBuilderProof.builderMonotone Symbol inferInstance arity I M N f τ P _ _ a b hMN
    (bitsMonotone above f τ hMN hab) hab

theorem valueWeakening {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I)
    {P Q : World I} (h : Extends P Q) (a : Inputs I f P) :
    RecursiveNaturalDomains.weaken h (markedValue above M f τ a)=markedValue above M f τ ((inputFamily I f).restrict h a) := by
  apply RecursiveNaturalDomainsProof.layerViewInjective I τ.val Q
  apply Subtype.ext
  rw [RecursiveNaturalDomainsProof.layerViewWeaken]
  change rawWeaken h (layerView I τ.val P (markedValue above M f τ a)).val=(layerView I τ.val Q (markedValue above M f τ ((inputFamily I f).restrict h a))).val
  rw [valueLayer,valueLayer,FunctionalTupleBuilderProof.builderWeakening Symbol inferInstance arity I M f τ P Q h _ a,bitsWeakening]

theorem naturalCoherentOutput : SourceConstructorOperatorTargets.NaturalCoherentOutput := by
  intro Symbol inst arity I above dec M
  constructor
  · intro f τ P a b hab
    exact valueMonotone above f τ le_rfl hab
  · intro f τ P Q h a
    exact valueWeakening above M f τ h a

theorem operatorMonotone : SourceConstructorOperatorTargets.OperatorMonotone := by
  intro Symbol inst arity I above dec M N hMN f τ P a
  exact valueMonotone above f τ hMN le_rfl

/-- Actual executable source F, with the fully proved coherent-family certificate. -/
def operator {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) : Constructors I :=
  ⟨operatorRaw above M,naturalCoherentOutput Symbol inferInstance arity I above inferInstance M⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorProof
