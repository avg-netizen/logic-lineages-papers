module
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerProof
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWSourceComparisonProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverNumericProof
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit.Proof
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

 theorem vectorAt_primitive : Primrec vectorAt := by
  have hr : Primrec (fun n : Nat => List.replicate n (SyntaxCode.typeCode Ty.ground)) := by
    have h := Primrec.list_map Primrec.list_range
      (Primrec.const (SyntaxCode.typeCode Ty.ground)).to₂
    apply h.of_eq
    intro n
    simp
  exact Primrec.option_bind
    (DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp ((hr.comp Primrec.fst).pair Primrec.snd))
    (OrdinalSyntax.ordinalSyntaxVectorCompilerPrimitiveRecursive.comp Primrec.snd).to₂

theorem flagPrimitiveRecursive : Targets.FlagPrimitiveRecursive := by
  have hn : Primrec (fun v : EncodedVector => v.2.map encodedClosedPositive) :=
    Primrec.list_map Primrec.snd (encodedClosedPositivePrimitiveRecursive.comp Primrec.snd)
  have hc : Primrec (fun p : EncodedVector × EncodedVector =>
      positiveComparison (p.1.2.map encodedClosedPositive) (p.2.2.map encodedClosedPositive)) :=
    positiveComparisonPrimitiveRecursive.comp (hn.comp Primrec.fst) (hn.comp Primrec.snd)
  have ha : Primrec (fun p : Nat×Nat×Nat => vectorAt (p.1,p.2.1)) :=
    vectorAt_primitive.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hb : Primrec (fun p : Nat×Nat×Nat => vectorAt (p.1,p.2.2)) :=
    vectorAt_primitive.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun p : Nat×Nat×Nat =>
      (vectorAt (p.1,p.2.1)).bind (fun a => (vectorAt (p.1,p.2.2)).map (fun b =>
        positiveComparison (a.2.map encodedClosedPositive) (b.2.map encodedClosedPositive)))) :=
    Primrec.option_bind ha (Primrec.option_map (hb.comp Primrec.fst)
      (hc.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂
  exact Primrec.option_getD.comp hp (Primrec.const false)

theorem context_codes (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) :
    Γ.map SyntaxCode.typeCode = List.replicate Γ.length (SyntaxCode.typeCode Ty.ground) := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
      have hs := hΓ σ (List.mem_cons_self)
      subst σ
      have ht : ∀ τ ∈ Γ, τ=Ty.ground := fun τ hτ => hΓ τ (List.mem_cons_of_mem _ hτ)
      simp only [List.map_cons,List.length_cons,List.replicate_succ,ih ht]

theorem vectorAt_typed {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v)
    (hc : compileVector v=some c) :
    vectorAt (Γ.length,SyntaxCode.encodeTerm t)=
      some (c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) := by
  unfold vectorAt
  rw [← context_codes Γ hΓ,DefaultSourceAssignment.Proof.assignmentCorrect Γ τ t,hv]
  simp only [Option.map_some,Option.bind_some]
  rw [OrdinalSyntax.ordinalSyntaxVectorCompilerCorrect Γ τ.level v,hc]
  rfl

theorem actualScalar : Targets.ActualScalar := by
  intro Γ hΓ τ t ρ
  obtain ⟨v,hv,c,hc,hs⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy t
  have hz := hs (fun x => ρ x+1) 0
  change (c.scalar.value (fun x => ρ x+1) : Ordinal)=
    denote (fun x => ((ρ x+1 : Nat) : Ordinal)) (v 0) at hz
  have he : scalarValue ρ t = c.scalar.value (fun x => ρ x+1) := by
    unfold scalarValue
    rw [hv]
    change OriginalDomain.finiteValue (denote (fun x => ((ρ x+1 : Nat) : Ordinal)) (v 0))=_
    rw [← hz]
    exact OriginalDomain.originalFiniteValueCalibration _
  refine ⟨v,hv,?_,?_⟩
  · rw [he]
    exact hz.symm
  · rw [he]
    exact AbsoluteObserver.Proof.scalar_positive c.scalar _ (fun x => by omega)

theorem positive_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c)
    (ρ : OrdinalComponent Γ → Nat) (j : Nat) :
    positiveNoteAt c.positiveNotes j = sourceVectorAtValue v ρ (j+1) := by
  by_cases hj : j < n
  · have h := compiledVectorSound Γ n v c hc ρ (Fin.succ ⟨j, hj⟩)
    simpa [positiveNoteAt, CompiledVector.positiveNotes, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hj, sourceVectorAtValue, ordinalVectorAt,
      Nat.succ_lt_succ hj, CompiledVector.value] using h
  · have hn : n ≤ j := Nat.le_of_not_gt hj
    have hp : (c.positiveNotes).length ≤ j := by simpa [CompiledVector.positiveNotes] using hn
    rw [positiveNoteAt, List.getD_eq_default _ _ hp]
    simp [sourceVectorAtValue, ordinalVectorAt, show ¬j+1<n+1 by omega, zeroNote, denote]

theorem normalized_positive {ι : Type} {n : Nat} (index : ι → Nat) (c : CompiledVector ι n) :
    (c.syntaxCode index).2.map encodedClosedPositive = normalCodes c.positiveNotes :=
  congrArg Prod.snd (vectorSyntaxNormalizationCorrect ι n index c)

theorem positiveFlagExact : Targets.PositiveFlagExact := by
  intro Γ hΓ τ υ a b ρ
  obtain ⟨av,ha,ac,hac,_⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy a
  obtain ⟨bv,hb,bc,hbc,_⟩ := actualSourceVectorCompilation Γ hΓ υ OrdinalSyntax.defaultPolicy b
  refine ⟨av,bv,ha,hb,?_⟩
  unfold positiveFlagCode
  rw [vectorAt_typed hΓ a av ac ha hac,vectorAt_typed hΓ b bv bc hb hbc]
  simp only [Option.bind_some,Option.map_some,Option.getD_some,normalized_positive]
  rw [positiveComparisonSourceCorrect]
  simp only [positive_field av ac hac (fun c => ρ c+1),positive_field bv bc hbc (fun c => ρ c+1)]

theorem querySplit : Targets.QuerySplit := by
  intro Γ hΓ τ υ a b ρ strict
  obtain ⟨av,bv,ha,hb,hflag⟩ := positiveFlagExact Γ hΓ τ υ a b ρ
  obtain ⟨aw,haw,hsa,_⟩ := actualScalar Γ hΓ τ a ρ
  obtain ⟨bw,hbw,hsb,_⟩ := actualScalar Γ hΓ υ b ρ
  rw [ha] at haw
  rw [hb] at hbw
  cases Option.some.inj haw
  cases Option.some.inj hbw
  have hsa0 : sourceVectorAtValue av (fun c => ρ c+1) 0 = (scalarValue ρ a : Ordinal) := by
    simpa [sourceVectorAtValue,ordinalVectorAt] using hsa
  have hsb0 : sourceVectorAtValue bv (fun c => ρ c+1) 0 = (scalarValue ρ b : Ordinal) := by
    simpa [sourceVectorAtValue,ordinalVectorAt] using hsb
  have hq : QueryAt strict a b ρ ↔ SourceComparisonAt strict av bv (fun c => ρ c+1) := by
    constructor
    · rintro ⟨ax,bx,hax,hbx,h⟩
      rw [ha] at hax
      rw [hb] at hbx
      cases Option.some.inj hax
      cases Option.some.inj hbx
      exact h
    · intro h
      exact ⟨av,bv,ha,hb,h⟩
  rw [hq,SourceComparisonAt,← hflag,hsa0,hsb0]
  cases strict <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.cast_lt,Nat.cast_le]
end LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit.Proof
