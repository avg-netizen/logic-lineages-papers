module
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceTargets
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
public import LogicLineages.OrdinalComparison.WWSourceForwardTranslationProof
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem programs : PolicySourceInterfaceTargets.Programs := by
  refine ⟨?_,encodedClosedPositivePrimitiveRecursive,scalarSyntaxValueComputable⟩
  intro p hp
  have hctx : Primrec (fun x : Nat × Nat => List.replicate x.1 0) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.fst (β := Nat)))
      (Primrec.const 0).to₂
    exact h.of_eq (fun x => by simp)
  have ha : Computable (fun x : Nat × Nat => PolicyAssignment.assignmentCode p (List.replicate x.1 0) x.2) :=
    (PolicyAssignmentRunPrograms.assignment p hp).comp (hctx.to_comp.pair Computable.snd)
  exact Computable.option_bind ha (ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp Computable.snd).to₂

theorem heads : PolicySourceInterfaceTargets.FixedHeads := by
  intro c
  obtain ⟨_,_,hp,hl,he⟩ := GeneralOmegaHeadLimit.Proof.actualClosedHeadCalibration c
  exact ⟨closedPositiveValuePositive c,hp,hl,he,scalarFixedShiftComputable c⟩

theorem code {p : Policy} {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    {τ : Ty} (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (ha : AdmissibleAssignment.assignment p t=some v) (hc : compileVector v=some c) :
    PolicySourceInterface.compile p Γ.length (SyntaxCode.encodeTerm t)=
      some (c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) := by
  have h := PolicyAssignmentSyntaxProof.literal p Γ τ t
  rw [ha,PolicySourceEqualityProof.context_codes Γ hΓ] at h
  simp only [Option.map_some] at h
  have k := ordinalSyntaxVectorCompilerCorrect Γ τ.level v
  rw [hc] at k
  simp only [Option.map_some] at k
  simp [PolicySourceInterface.compile,h,k]

theorem typed : PolicySourceInterfaceTargets.TypedInterface := by
  intro p Γ hΓ τ t
  obtain ⟨v,ha,c,hc,he⟩ := actualSourceVectorCompilation Γ hΓ τ p t
  refine ⟨v,c,ha,hc,code hΓ t v c ha hc,?_,?_,?_,?_⟩
  · obtain ⟨v',ha',hpos,_⟩ := actualSourceForwardTranslation.2.2 Γ hΓ τ p t
    have hv : v=v' := Option.some.inj (ha.symm.trans ha')
    subst v'
    intro j hj
    obtain ⟨hv,z,hz,hp,hs⟩ := hpos j hj
    exact ⟨hv,z,hz,hp,encodedClosedPositiveCorrect z,fun s => (hs (valuation s)).symm⟩
  · intro s
    obtain ⟨ρ,hp,hv⟩ := DefaultSourceDomainProof.domain.2 Γ hΓ s
    refine ⟨ρ,hp,hv,?_⟩
    intro j
    have hh : valuation s = fun x => (ρ x : Ordinal) := funext hv
    simpa only [expressionValue,hh] using he ρ j
  · intro ρ hp
    obtain ⟨s,hv⟩ := DefaultSourceDomainProof.domain.1 Γ hΓ ρ hp
    refine ⟨s,hv,?_⟩
    intro j
    have hh : valuation s = fun x => (ρ x : Ordinal) := funext hv
    simpa only [expressionValue,hh] using he ρ j
  · intro xs
    exact scalarSyntaxValueSourceCorrect _ _ c.scalar xs

theorem raw : PolicySourceInterfaceTargets.RawInterface := by
  intro p d n out
  let Γ := List.replicate d Ty.ground
  have hg : ∀ σ ∈ Γ, σ=Ty.ground := by simp [Γ]
  have hl : Γ.length=d := by simp [Γ]
  constructor
  · intro h
    obtain ⟨v,ha,hc⟩ : ∃ v,
        PolicyAssignment.assignmentCode p (List.replicate d 0) n=some v ∧ compileVectorCode v=some out := by
      simpa only [PolicySourceInterface.compile,bind,Option.bind_eq_some_iff] using h
    have hac : PolicyAssignment.assignmentCode p (Γ.map SyntaxCode.typeCode) n=some v := by
      rw [PolicySourceEqualityProof.context_codes Γ hg,hl]; exact ha
    obtain ⟨τ,t,w,ht,hw,hv⟩ := (PolicyAssignmentSyntaxProof.sourceExact p Γ n v).mp hac
    obtain ⟨w',hw',c,hc',_⟩ := actualSourceVectorCompilation Γ hg τ p t
    have ew : w=w' := Option.some.inj (hw.symm.trans hw')
    subst w'
    have k := ordinalSyntaxVectorCompilerCorrect Γ τ.level w
    rw [hc',Option.map_some,hv,hc] at k
    exact ⟨τ,t,w,c,ht,hw,hc',(Option.some.inj k).symm⟩
  · rintro ⟨τ,t,v,c,ht,ha,hc,ho⟩
    have h := code hg t v c ha hc
    have hfinal := h.trans (congrArg some ho)
    simpa only [hl,ht] using hfinal
end LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
