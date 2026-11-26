module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterSyntaxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence PrimitiveLowering
open CurrentDecisionEmitter
open RawSourceDAG (Code encode variableIndex)
open RawSourceDAG.InputCompiler (encodeInput)
open RawSourceDAG.Operations (renamingCode rename_input renameCode)
open RawSourceDAG.BinaryPlanCompiler (prefixTable prefix_table_code)

theorem factor_exact {Γ τ} (d : Input Γ τ) :
    factorCode (encode ⟨Γ,τ,d⟩) = AbsoluteObserver.factor τ := by
  change 2*(SyntaxCode.typeLevel (SyntaxCode.typeCode τ)+1)+1 = _
  rw [SyntaxCode.Proof.typeLevelExact]
  rfl

private theorem place_table {Γ} (right : Bool) :
    renamingCode (place (Γ:=Γ) right) =
      (if right then [2,3] else [0,1]) ++ prefixTable 6 (Γ.map SyntaxCode.typeCode) := by
  cases right
  · change 0 :: 1 :: renamingCode (shift 6 (Γ:=Γ)) = _
    rw [prefix_table_code]
    rfl
  · change 2 :: 3 :: renamingCode (shift 6 (Γ:=Γ)) = _
    rw [prefix_table_code]
    rfl

theorem probes_exact {Γ τ} (right : Bool) (hg : ∀ t ∈ Γ, t = Ty.ground) (d : Input Γ τ) :
    probeCodes right (encode ⟨Γ,τ,d⟩) =
      (encode ⟨Extension Γ,.ground,(probes right hg d).1⟩,
       encode ⟨Extension Γ,.ground,(probes right hg d).2⟩) := by
  let ctx := Γ.map SyntaxCode.typeCode
  let Γ₂ := Ty.ground :: Ty.ground :: Γ
  let d₂ := ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) d
  let c₂ := ScopedDAG.renameInput (AbsoluteObserver.fromEmpty Γ₂) (AbsoluteProbeDAG.closeInput hg d)
  have h₂ : liftCode 2 (encode ⟨Γ,τ,d⟩) = encode ⟨Γ₂,τ,d₂⟩ := lift_exact d 2
  have hc₂ : renameCode (0::0::ctx) [] (CurrentProbeCode.closeRaw (encode ⟨Γ,τ,d⟩)) =
      encode ⟨Γ₂,τ,c₂⟩ := by
    rw [CurrentProbeCode.exactClosing Γ τ hg d]
    exact (rename_input (AbsoluteObserver.fromEmpty Γ₂) (AbsoluteProbeDAG.closeInput hg d)).symm
  unfold probes probeCodes
  dsimp only
  change (renameCode _ _ (CurrentProbeCode.probeRaw (liftCode 2 _) 0),
    renameCode _ _ (CurrentProbeCode.probeRaw (renameCode (0::0::ctx) [] (CurrentProbeCode.closeRaw _)) 1)) = _
  rw [h₂, hc₂]
  have hl := CurrentProbeCode.exactProbe Γ₂ τ d₂ .here
  have hr := CurrentProbeCode.exactProbe Γ₂ τ c₂ (.there .here)
  change CurrentProbeCode.probeRaw (encode ⟨Γ₂,τ,d₂⟩) 0 =
    encode ⟨Γ₂,.ground,AbsoluteProbeDAG.originalInput d⟩ at hl
  change CurrentProbeCode.probeRaw (encode ⟨Γ₂,τ,c₂⟩) 1 =
    encode ⟨Γ₂,.ground,AbsoluteProbeDAG.closedInput hg d⟩ at hr
  rw [hl,hr,rename_input,rename_input,place_table]
  simp [Extension,SyntaxCode.typeCode,ctx]

private theorem shifted_codes {Γ Δ τ} (r : Renaming Γ Δ) (n : Nat)
    (h : ∀ (τ : Ty) (x : Variable Γ τ), variableIndex (r x) = variableIndex x+n)
    (hΓ : Δ.map SyntaxCode.typeCode = List.replicate n 0 ++ Γ.map SyntaxCode.typeCode)
    (d : Input Γ τ) :
    encode ⟨Δ,τ,ScopedDAG.renameInput r d⟩ = liftCode n (encode ⟨Γ,τ,d⟩) := by
  rw [rename_input, hΓ, renaming_by_index r n h]
  rfl

private theorem indices_shift {Γ Δ} (s : Renaming Γ Δ) (n : Nat)
    (hs : ∀ (τ : Ty) (i : Variable Γ τ), variableIndex (s i) = variableIndex i+n)
    (p : Ports Γ) :
    portIndices (mapPorts s p) =
      ((portIndices p).1+n,(portIndices p).2.1+n,(portIndices p).2.2.1+n,(portIndices p).2.2.2+n) := by
  simp only [portIndices,mapPorts,hs]

theorem counter_syntax (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool) {Γ σ τ}
    (hg : ∀ t ∈ Γ, t = Ty.ground) (a : Input Γ σ) (b : Input Γ τ) :
    let codeA := encode ⟨Γ,σ,a⟩
    let codeB := encode ⟨Γ,τ,b⟩
    encodeInput (counterProgram strict hg a b (CurrentAbsolute.anchor p f codeA) (CurrentAbsolute.anchor p f codeB)) =
      counterCode p f (strict,codeA,codeB) := by
  dsimp only
  let G := Extension Γ
  let L := probes false hg a
  let R := probes true hg b
  let i := AbsoluteObserver.factor σ
  let j := AbsoluteObserver.factor τ
  let A := CurrentAbsolute.anchor p f (encode ⟨Γ,σ,a⟩)
  let B := CurrentAbsolute.anchor p f (encode ⟨Γ,τ,b⟩)
  let x : Variable G .ground := fresh 0
  let y : Variable G .ground := fresh 1
  let u : Variable G .ground := fresh 2
  let w : Variable G .ground := fresh 3
  let av : Variable G .ground := fresh 4
  let bv : Variable G .ground := fresh 5
  let k : ∀ {Δ}, Renaming G Δ → Ports Δ → InputNormalization.Input Δ 0 := fun r l =>
    observe (ScopedDAG.renameInput r R.1) (ScopedDAG.renameInput r R.2)
      (r u) (r w) (r bv) j B
      (fun s t => finalRows strict (mapPorts s l) t (s (r av)) (s (r bv)))
  obtain ⟨Δ,r,l,ht,hr,hl,he⟩ := observe_syntax L.1 L.2 x y av i A k
  change encodeInput (observe L.1 L.2 x y av i A k) = _
  rw [he]
  let last : ∀ {Ξ}, Renaming Δ Ξ → Ports Ξ → InputNormalization.Input Ξ 0 :=
    fun s t => finalRows strict (mapPorts s l) t (s (r av)) (s (r bv))
  obtain ⟨Ξ,s,t,_,hs,hb,he'⟩ := observe_syntax
    (ScopedDAG.renameInput r R.1) (ScopedDAG.renameInput r R.2) (r u) (r w) (r bv) j B last
  change (observeSteps (encode ⟨G,.ground,L.1⟩) (encode ⟨G,.ground,L.2⟩) 0 1 4 i A ++
    (encodeInput (observe (ScopedDAG.renameInput r R.1) (ScopedDAG.renameInput r R.2)
      (r u) (r w) (r bv) j B last)).1,
    (encodeInput (observe (ScopedDAG.renameInput r R.1) (ScopedDAG.renameInput r R.2)
      (r u) (r w) (r bv) j B last)).2) = _
  rw [he', shifted_codes r (i+5) hr ht R.1, shifted_codes r (i+5) hr ht R.2]
  change (_ ++ (_ ++ (encodeInput (finalRows strict (mapPorts s l) t (s (r av)) (s (r bv)))).1),
    (encodeInput (finalRows strict (mapPorts s l) t (s (r av)) (s (r bv)))).2) = _
  rw [rows_exact, indices_shift s (j+5) hs l, hl, hb]
  have ha0 : variableIndex (r u) = 2+(i+5) := hr .ground u
  have ha1 : variableIndex (r w) = 3+(i+5) := hr .ground w
  have ha2 : variableIndex (r bv) = 5+(i+5) := hr .ground bv
  have ha3 : variableIndex (s (r av)) = 4+(i+5)+(j+5) := by rw [hs,hr]; rfl
  have ha4 : variableIndex (s (r bv)) = 5+(i+5)+(j+5) := by rw [hs,hr]; rfl
  unfold counterCode
  dsimp only
  rw [probes_exact false hg a, probes_exact true hg b, factor_exact, factor_exact,
    ha0,ha1,ha2,ha3,ha4]
  simp only [i,j,A,B,L,R,G,List.append_assoc]
  rfl

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
