module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets FullTuplePacking CoherentConstructorLattice FunctionalTupleBuilder

theorem appendInputMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {f : HeadIndex I} {P : World I} {a b : Inputs I f P} {xs ys : List (Packed I P)}
    (hab : a ≤ b) (hxy : TypedExtraAppend.Dominated xs ys) : appendInput a xs ≤ appendInput b ys := by
  constructor
  · exact hab.1
  · intro τ
    exact TypedExtraAppendProof.appendMonotone Symbol inferInstance arity I P a.2 b.2 xs ys hab.2 hxy τ

theorem appendInputRestriction {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {f : HeadIndex I} {P Q : World I} (h : Extends P Q) (a : Inputs I f P) (xs : List (Packed I P)) :
    (inputFamily I f).restrict h (appendInput a xs)=appendInput ((inputFamily I f).restrict h a) (xs.map (packedWeaken h)) := by
  apply Prod.ext
  · rfl
  · funext τ
    apply Subtype.ext
    exact TypedExtraAppendProof.restrictionAppend Symbol inferInstance arity I P Q h a.2 xs τ

theorem fullTableCalibration : FunctionalTupleBuilderTargets.FullTableCalibration := by
  intro Symbol inst arity I M f τ P bits a Q s v
  rfl

theorem naturalTables : FunctionalTupleBuilderTargets.NaturalTables := by
  intro Symbol inst arity I M f τ P bits a
  constructor
  · intro Q s v w hvw
    apply M.property.1
    exact appendInputMonotone le_rfl (FullTuplePackingProof.pointwiseDomination Symbol inst arity I τ s Q.val v w hvw)
  · intro Q R h s v
    change RecursiveNaturalDomains.weaken h (M.val f (resultTag I τ s) Q.val _)=M.val f (resultTag I τ s) R.val _
    rw [M.property.2]
    rw [appendInputRestriction,FullTuplePackingProof.weakeningMap Symbol inst arity I τ s Q.val R.val h v]
    rw [(inputFamily I f).restrictComposition]

theorem builderMonotone : FunctionalTupleBuilderTargets.BuilderMonotone := by
  intro Symbol inst arity I M N f τ P bits bits' a b hMN hbits hab
  constructor
  · exact hbits
  · intro Q s v
    apply le_trans (hMN f (resultTag I τ s) Q.val _)
    apply N.property.1
    apply appendInputMonotone ((inputFamily I f).restrictMonotone P Q.val Q.property a b hab)
    intro p hp
    exact ⟨p,hp,(TypedExtraDownsetsProof.packedOrder Symbol inst arity I Q.val).1 p⟩

theorem builderWeakening : FunctionalTupleBuilderTargets.BuilderWeakening := by
  intro Symbol inst arity I M f τ P Q h bits a
  apply Prod.ext
  · rfl
  · funext R s v
    change M.val f (resultTag I τ s) R.val _=M.val f (resultTag I τ s) R.val _
    rw [(inputFamily I f).restrictComposition]

theorem actualValueRealization : FunctionalTupleBuilderTargets.ActualValueRealization := by
  intro Symbol inst arity I M f τ P bits a
  let v : Natural I τ.val (lower I τ.val) P := ⟨buildRaw M f τ bits a,naturalTables Symbol inst arity I M f τ P bits a⟩
  refine ⟨layerFold I τ.val P v,?_⟩
  rw [RecursiveNaturalDomainsProof.layerViewFold]

def buildValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) {P : World I}
    (bits : Bits I τ.val P) (a : Inputs I f P) : Value I τ.val P :=
  layerFold I τ.val P ⟨buildRaw M f τ bits a,naturalTables Symbol inferInstance arity I M f τ P bits a⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderProof
