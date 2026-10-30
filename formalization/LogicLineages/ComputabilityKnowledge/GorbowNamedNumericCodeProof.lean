module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedNumericCode
public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowRawContextBoundProof
public import LogicLineages.ComputabilityKnowledge.GorbowContextSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCodeProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowNamedBindingCode GorbowNamedNumericCode
open GorbowCodeConstructors GorbowRawContextBound

private theorem decodeNumber (raw : List Nat) : GorbowNumericCertificate.decodeFormula (number raw)=some raw :=
  (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl

private theorem namesFromSupport (n : Nat) (φ : Formula n) (v : Fin n) (hs : formulaSupport φ={v.val}) :
    GorbowSupportCode.formulaNames n (GorbowFormulaPrefixCode.encode φ)=some [v.val] := by
  have h := (GorbowNamedBindingCodeProof.exactSelection n v.val _ _).mpr ⟨v.isLt,φ,rfl,hs,rfl⟩
  unfold selectCode at h
  split at h
  · rename_i hg
    exact hg.2
  · simp at h

private theorem supportFromNames (n : Nat) (φ : Formula n) (v : Nat)
    (h : GorbowSupportCode.formulaNames n (GorbowFormulaPrefixCode.encode φ)=some [v]) :
    formulaSupport φ={v} := by
  obtain ⟨ψ,he,hn⟩ := (GorbowSupportCodeProof.exactNames.2 n _ _).mp h
  have hp : φ=ψ := GorbowFormulaPrefixCodeProof.encodingInjective n he
  subst ψ
  apply Finset.ext
  intro i
  have hb := GorbowFreeSupportProof.supportBound.2 n φ i
  have hm := congrArg (fun xs : List Nat => i∈xs) hn
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.mem_filter,List.mem_range,decide_eq_true_eq] at hm
  simpa only [Finset.mem_singleton] using ((Iff.of_eq hm).trans (and_iff_right_of_imp hb)).symm

private theorem inferred (n : Nat) (φ : Formula n) (v : Fin n) (hs : formulaSupport φ={v.val}) :
    ∃ (hv : v.val<rawBound (GorbowFormulaPrefixCode.encode φ))
      (ψ : Formula (rawBound (GorbowFormulaPrefixCode.encode φ))),
      GorbowContextTransport.formula _ φ=some ψ ∧
      GorbowFormulaPrefixCode.encode ψ=GorbowFormulaPrefixCode.encode φ ∧ formulaSupport ψ={v.val} := by
  have hv := GorbowRawContextBoundProof.supportBound.2 n φ v.val (by simp [hs])
  obtain ⟨ψ,hψ,he,hsp⟩ := GorbowRawContextBoundProof.typedTransport.2 n φ
  exact ⟨hv,ψ,hψ,he,hsp.trans hs⟩

private theorem inputEncoded (n : Nat) (φ : Formula n) (v : Fin n) (hs : formulaSupport φ={v.val}) :
    namedInput v.val (formulaNumber φ)=some (GorbowFormulaPrefixCode.encode φ) := by
  obtain ⟨hv,ψ,hψ,he,hsp⟩ := inferred n φ v hs
  have hn := namesFromSupport _ ψ ⟨v.val,hv⟩ hsp
  rw [he] at hn
  simp [namedInput,formulaNumber,decodeNumber,hv,hn]

theorem exactInput : Comparators.GorbowNamedNumericCode.ExactInput := by
  intro v code raw
  constructor
  · intro h
    cases hd : GorbowNumericCertificate.decodeFormula code with
    | none => simp [namedInput,hd] at h
    | some xs =>
      simp only [namedInput,hd,bind,Option.bind_some] at h
      split at h
      · rename_i hg
        have he : xs=raw := Option.some.inj h
        subst xs
        obtain ⟨φ,hφ,hn⟩ := (GorbowSupportCodeProof.exactNames.2 (rawBound raw) raw [v]).mp hg.2
        have hs : formulaSupport φ={v} := supportFromNames _ φ v (by simpa [hφ] using hg.2)
        have hc := (GorbowNumericCertificateProof.exactDecoding.1 code raw).mp hd
        exact ⟨rawBound raw,φ,hg.1,by simpa [formulaNumber,number,hφ] using hc.symm,hs,hφ⟩
      · simp at h
  · rintro ⟨n,φ,hv,rfl,hs,rfl⟩
    exact inputEncoded n φ ⟨v,hv⟩ hs

theorem originalCalibration : Comparators.GorbowNamedNumericCode.OriginalCalibration := by
  intro n φ v hs
  obtain ⟨hv,ψ,hψ,he,hsp⟩ := inferred n φ v hs
  let w : Fin (rawBound (GorbowFormulaPrefixCode.encode φ)) := ⟨v.val,hv⟩
  have ha := (GorbowNamedBindingCodeProof.exactBinding _ w.val _ _).1.mpr ⟨w.isLt,ψ,he.symm,rfl⟩
  have hx := (GorbowNamedBindingCodeProof.exactBinding _ w.val _ _).2.mpr ⟨w.isLt,ψ,he.symm,rfl⟩
  have hsel := (GorbowNamedBindingCodeProof.exactSelection _ w.val _ _).mpr ⟨w.isLt,ψ,he.symm,hsp,rfl⟩
  obtain ⟨hea,hex,hes⟩ := GorbowContextSubstitutionProof.namedEncoding n _ v w rfl φ ψ hψ
  have hin := inputEncoded n φ v hs
  refine ⟨hin,?_,?_,?_⟩
  · change (do let raw ← namedInput v.val (formulaNumber φ); let out ← bindAllCode (rawBound raw) v.val raw; pure (number out))=_
    rw [hin]
    simp only [bind,Option.bind_some]
    rw [ha]
    simp only [bind,Option.bind_some,pure,Option.pure_def,formulaNumber,← hea]
  · change (do let raw ← namedInput v.val (formulaNumber φ); let out ← bindExCode (rawBound raw) v.val raw; pure (number out))=_
    rw [hin]
    simp only [bind,Option.bind_some]
    rw [hx]
    simp only [bind,Option.bind_some,pure,Option.pure_def,formulaNumber,← hex]
  · rw [selectNumber,hin]
    simp only [bind,Option.bind_some]
    rw [hsel]
    simp only [bind,Option.bind_some,pure,Option.pure_def,formulaNumber,← hes]

theorem originalSemantics : Comparators.GorbowNamedNumericCode.OriginalSemantics := by
  intro n φ v hs
  obtain ⟨σ,τ,hσ,hτ,heσ,heτ,hsem⟩ := GorbowContextTransportProof.namedClosure n v φ hs
  let A : Selector := ⟨selectVariable v φ,(GorbowNamedBindingProof.selectionSupport n v φ hs).2⟩
  obtain ⟨hin,ha,hx,hsel⟩ := originalCalibration n φ v hs
  have hna : formulaNumber (bindAll v φ)=formulaNumber σ := congrArg number heσ.symm
  have hnx : formulaNumber (bindEx v φ)=formulaNumber τ := congrArg number heτ.symm
  refine ⟨σ,τ,A,by simpa only [hna] using ha,by simpa only [hnx] using hx,hsel,?_⟩
  intro I ρ
  exact ⟨(hsem I ρ).1,(hsem I ρ).2,GorbowNamedBindingProof.selectionSemantics n v φ hs I ρ⟩

private theorem outerDomain (v code : Nat) (f : List Nat → Option Nat) (out : Nat)
    (h : (namedInput v code >>= f)=some out) : ∃ raw,namedInput v code=some raw := by
  cases he : namedInput v code with
  | none => simp [he] at h
  | some raw => exact ⟨raw,rfl⟩

theorem outputDomains : Comparators.GorbowNamedNumericCode.OutputDomains := by
  intro v code out
  constructor
  · intro h
    obtain ⟨raw,hr⟩ := outerDomain v code _ out h
    obtain ⟨n,φ,hv,hcode,hs,he⟩ := (exactInput v code raw).mp hr
    subst code
    obtain ⟨σ,τ,A,ha,hx,hsel,hsem⟩ := originalSemantics n φ ⟨v,hv⟩ hs
    rw [ha] at h
    exact ⟨σ,(Option.some.inj h).symm⟩
  constructor
  · intro h
    obtain ⟨raw,hr⟩ := outerDomain v code _ out h
    obtain ⟨n,φ,hv,hcode,hs,he⟩ := (exactInput v code raw).mp hr
    subst code
    obtain ⟨σ,τ,A,ha,hx,hsel,hsem⟩ := originalSemantics n φ ⟨v,hv⟩ hs
    rw [hx] at h
    exact ⟨τ,(Option.some.inj h).symm⟩
  · intro h
    obtain ⟨raw,hr⟩ := outerDomain v code _ out h
    obtain ⟨n,φ,hv,hcode,hs,he⟩ := (exactInput v code raw).mp hr
    subst code
    obtain ⟨σ,τ,A,ha,hx,hsel,hsem⟩ := originalSemantics n φ ⟨v,hv⟩ hs
    rw [hsel] at h
    exact ⟨A,(Option.some.inj h).symm⟩

theorem exactRejection : Comparators.GorbowNamedNumericCode.ExactRejection := by
  intro v code
  cases hi : namedInput v code with
  | none => simp [allNumber,exNumber,bindNumber,selectNumber,hi]
  | some raw =>
    obtain ⟨n,φ,hv,hcode,hs,he⟩ := (exactInput v code raw).mp hi
    subst code
    obtain ⟨hin,ha,hx,hsel⟩ := originalCalibration n φ ⟨v,hv⟩ hs
    simp only [ha,hx,hsel,hi,Option.some_ne_none,false_iff,and_self]

private theorem pr_namedInput : Primrec (fun p : Nat × Nat => namedInput p.1 p.2) := by
  have hv : Primrec (fun p : (Nat × Nat) × List Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hb := GorbowRawContextBoundProof.uniformPrograms.1.comp (Primrec.snd : Primrec (fun p : (Nat × Nat) × List Nat => p.2))
  have hn := GorbowSupportCodeProof.uniformPrograms.2.2.2.2.1.comp (hb.pair Primrec.snd)
  have hw := Primrec.option_some.comp (Primrec.list_cons.comp hv (Primrec.const []))
  have hg := (Primrec.nat_lt.comp hv hb).and (Primrec.eq.comp hn hw)
  have hbody := Primrec.ite hg (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind (GorbowNumericCertificateProof.uniformPrograms.1.comp Primrec.snd) hbody.to₂

private theorem pr_output (f : Nat → Nat → List Nat → Option (List Nat))
    (hf : Primrec (fun p : Nat × Nat × List Nat => f p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Nat × Nat => do
      let raw ← namedInput p.1 p.2
      let out ← f (rawBound raw) p.1 raw
      pure (number out)) := by
  have hb := GorbowRawContextBoundProof.uniformPrograms.1.comp (Primrec.snd : Primrec (fun p : (Nat × Nat) × List Nat => p.2))
  have hv : Primrec (fun p : (Nat × Nat) × List Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hinner := hf.comp (hb.pair (hv.pair Primrec.snd))
  have hmap := Primrec.option_map hinner (GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2.comp Primrec.snd).to₂
  have h := Primrec.option_bind pr_namedInput hmap.to₂
  apply h.of_eq
  intro p
  cases hn : namedInput p.1 p.2 with
  | none => simp [hn]
  | some raw => cases ho : f (rawBound raw) p.1 raw <;> simp [hn,ho]

theorem uniformPrograms : Comparators.GorbowNamedNumericCode.UniformPrograms :=
  ⟨pr_namedInput,pr_output bindAllCode GorbowNamedBindingCodeProof.uniformPrograms.2.2.1,
    pr_output bindExCode GorbowNamedBindingCodeProof.uniformPrograms.2.2.2.1,
    pr_output selectCode GorbowNamedBindingCodeProof.uniformPrograms.2.2.2.2⟩
theorem gorbowNamedNumericCode : Comparators.GorbowNamedNumericCode.Target :=
  ⟨exactInput,originalCalibration,outputDomains,originalSemantics,exactRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCodeProof
