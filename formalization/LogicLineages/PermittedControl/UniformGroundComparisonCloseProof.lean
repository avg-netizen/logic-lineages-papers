module
public import LogicLineages.PermittedControl.UniformGroundComparisonTargets
import LogicLineages.PermittedControl.ControlProof
import LogicLineages.PermittedControl.NearControlProof
import LogicLineages.PermittedControl.SelectedFunctionalHardnessProof
import LogicLineages.PermittedControl.SelectedFiniteQueryProof
import LogicLineages.PermittedControl.SelectedSingleQueryProof
import LogicLineages.PermittedControl.PolicySuppliedCodeRealizationProof

public section
namespace LogicLineages.PermittedControl.UniformGroundComparison
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain
open PolicySuppliedCodeMacro (RealizesPolicy)

/-- Fixing a realizing program turns the uniform procedure into a total
computable decider for that policy. -/
private theorem perPolicy (ctrl : Nat → Nat) (uniform : UniformGroundDecidable ctrl) :
    GroundComparison.GroundDecidable ctrl := by
  intro p effective rel
  obtain ⟨decide,partrec,spec⟩ := uniform rel
  obtain ⟨e,realizes⟩ := PolicySuppliedCodeRealization.effectiveHasCode p effective
  obtain ⟨halts,correct⟩ := spec e p realizes
  refine ⟨fun x => (decide (e,x.1,x.2.1,x.2.2)).get (halts x.1 x.2.1 x.2.2),?_,?_⟩
  · have inputs : Computable (fun x : Nat × Nat × Nat => ((e,x.1,x.2.1,x.2.2) : GroundArgs)) :=
      Computable.pair (Computable.const e) (Computable.pair Computable.fst
        (Computable.pair (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
    have run : Partrec (fun x : Nat × Nat × Nat => decide (e,x.1,x.2.1,x.2.2)) :=
      partrec.comp inputs
    exact run.of_eq_tot (fun x => Part.get_mem _)
  · intro Γ ground τ υ a b
    obtain ⟨answer,value,meaning⟩ := correct Γ ground τ υ a b
    have member : answer ∈ decide (e,Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) := by
      rw [value]
      exact Part.mem_some _
    have same := Part.get_eq_of_mem member
      (halts Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b))
    show (decide (e,Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)).get _ = true ↔ _
    rw [same]
    exact meaning

/-- Fixing the near-control parameter. -/
private theorem nearAt (uniform : UniformNearGroundDecidable) (bound : Nat) :
    UniformGroundDecidable (nearControl bound) := by
  intro rel
  obtain ⟨decide,partrec,spec⟩ := uniform rel
  refine ⟨fun x => decide (bound,x),?_,?_⟩
  · have inputs : Computable (fun x : GroundArgs => ((bound,x) : NearArgs)) :=
      Computable.pair (Computable.const bound) Computable.id
    exact partrec.comp inputs
  · intro e p realizes
    exact spec bound e p realizes

theorem uniformImpliesGround : UniformImpliesGround := by
  intro uniform
  exact ⟨perPolicy _ uniform.1,fun bound => perPolicy _ (nearAt uniform.2 bound)⟩

/-- Everything in the strengthened `thm:main` comparator except clause (i)
is already accepted: the control laws, the near-control modular bound, the
functional hardness statements, and the literal reduction programs with
their exact total reductions. -/
theorem uniformMainFromGround (uniform : UniformGroundComparison) : UniformMainComparison :=
  ⟨fullControl,nearControlModular,uniform,
    SelectedFunctionalHardness.Proof.selectedFunctionalHardness,
    SelectedFiniteQuery.Proof.literalProgram,SelectedFiniteQuery.Proof.exactTotalReduction,
    SelectedSingleQuery.Proof.selectedSingleQuery.1,SelectedSingleQuery.Proof.exactTotalReduction⟩

#print axioms uniformImpliesGround
#print axioms uniformMainFromGround
end LogicLineages.PermittedControl.UniformGroundComparison
