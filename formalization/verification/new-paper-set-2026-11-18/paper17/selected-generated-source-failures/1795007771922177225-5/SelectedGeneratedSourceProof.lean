module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceHeadsProof
public import LogicLineages.PermittedControl.SelectedCanonicalDomainProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedSourceProof
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleAssignment
open SelectedGeneratedSource SelectedGeneratedSourceSoundProof

private theorem vectorSound (ctrl : Nat → Nat) (Γ : List Ty) (n : Nat)
    (v : OrdinalVector Γ n) (c : CompiledVector (OrdinalComponent Γ) n)
    (hc : compileVector v = some c) : ∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
      vectorValueWith ctrl c ρ j = ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) (v j) := by
  obtain ⟨s,hs,p,hp,he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, collect n (fun j => extractPositive (v j.succ)) = some p ∧ CompiledVector.mk s p = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
  subst c
  intro ρ j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact scalarSound ctrl Γ (v 0) s hs ρ
  · exact closedSound ctrl Γ (v k.succ) (p k)
      (SelectedBoundedDeltaProof.collect_success _ _ _ hp k) (fun x => (ρ x : Ordinal))

theorem typedImage : SelectedGeneratedSourceTargets.TypedImage := by
  intro ctrl K hctrl p Γ hΓ τ t
  obtain ⟨v,ha,hcode,hg,hgrade,hbound⟩ := SelectedCanonicalDomainProof.canonicalAssignment ctrl K hctrl Γ τ p t
  obtain ⟨c,hc⟩ := generatedGroundVectorCompilationTotal Γ hΓ τ.level v hg
  refine ⟨v,c,ha,hc,StandardControlCurrent.PolicySourceInterfaceProof.code hΓ t v c ha hc,?_,
    vectorSound ctrl Γ τ.level v c hc,?_⟩
  · intro j hj
    have hz := actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (hg j)
    obtain ⟨z,he⟩ := generatedClosedPositiveEvaluationTotal Γ j.val (v j) (hg j) hj hz
    exact ⟨hz,z,he,closedPositiveValuePositive z,encodedClosedPositiveCorrect z,
      fun ρ => (closedSound ctrl Γ (v j) z he ρ).symm⟩
  · intro ρ hp
    exact SelectedGeneratedSourceHeadsProof.scalarPositive ctrl K hctrl c.scalar ρ hp

theorem fullSelectedGeneratedSource : SelectedGeneratedSourceTargets.FullSelectedGeneratedSource :=
  ⟨closedSound, scalarSound, SelectedGeneratedSourceHeadsProof.fixedHeads,
    SelectedGeneratedSourceHeadsProof.circuitComputable,
    StandardControlCurrent.PolicySourceInterfaceProof.programs.1,
    StandardControlCurrent.PolicySourceInterfaceProof.programs.2.1,
    typedImage, StandardControlCurrent.PolicySourceInterfaceProof.raw⟩

end LogicLineages.PermittedControl.SelectedGeneratedSourceProof
