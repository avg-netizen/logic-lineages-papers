module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataTargets
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeStructureProof
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationStructureProof
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Proof
open ActiveScalarAnnotation AdditiveHeadTree
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem exactCertificates : Targets.ExactCertificates := by
  intro k Γ F d hd
  induction d with
  | free q => exact ⟨.free hd.1 hd.2,.free hd.2⟩
  | tracked => exact ⟨.tracked,.tracked⟩
  | add a b iha ihb =>
    have ha := iha hd.1
    have hb := ihb hd.2
    exact ⟨.add ha.1 hb.1,.add ha.2 hb.2⟩
  | collapse op tail ih =>
    have ht := ih hd.2.2.2
    have hop : GroundOperatorDischarge.OperatorWitness OrdinalSyntax.defaultPolicy op.head :=
      ⟨op.arity,op.source,op.vector,hd.1,rfl⟩
    exact ⟨.collapse hd.2.1 ht.1,.collapse hop hd.2.2.1 ht.2⟩

theorem close_erase {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) :
    erase (closeTree d) = ordinalHeadClosure (erase d) := by
  induction d with
  | free q | tracked => rfl
  | add a b iha ihb =>
    change (.add (erase (closeTree a)) (erase (closeTree b)) : OrdinalExpression Γ) =
      .add (ordinalHeadClosure (erase a)) (ordinalHeadClosure (erase b))
    rw [iha,ihb]
  | collapse op tail ih =>
    change (.collapse (ordinalHeadClosure op.head) (erase (closeTree tail)) : OrdinalExpression Γ) =
      .collapse (ordinalHeadClosure op.head) (ordinalHeadClosure (erase tail))
    rw [ih]

theorem closeOperator_assignment {Γ} (op : Operator (.ground :: Γ))
    (hop : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (closeOperator op).source =
      some (closeOperator op).vector := by
  change AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
    (GroundOperatorDischarge.close op.source) = some (fun j => ordinalHeadClosure (op.vector j))
  rw [GroundOperatorDischarge.Proof.wholeAssignment,hop]
  rfl

theorem close_valid {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hd : Valid d) : Valid (closeTree d) := by
  induction d with
  | free q =>
    exact ⟨actualGeneratedGradeHeadClosure Γ .ground 0 q hd.1,
      fun ha => hd.2 ((ActiveScalarAnnotation.Proof.active_headClosure F q).mp ha)⟩
  | tracked => trivial
  | add a b iha ihb => exact ⟨iha hd.1,ihb hd.2⟩
  | collapse op tail ih =>
    refine ⟨closeOperator_assignment op hd.1,
      AdditiveHeadTree.Proof.headClosureHead k Γ F op.head hd.2.1,?_,ih hd.2.2.2⟩
    intro ha
    have hhead : Active (.there F) op.head :=
      (ActiveScalarAnnotation.Proof.active_headClosure F op.head).mp ha
    have htail := hd.2.2.1 hhead
    rw [close_erase]
    exact (ActiveScalarAnnotation.Proof.active_headClosure F (erase tail)).mpr htail

theorem exactGroundClosure : Targets.ExactGroundClosure := by
  intro k Γ F d
  exact ⟨close_erase d,close_valid d⟩

end LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Proof
