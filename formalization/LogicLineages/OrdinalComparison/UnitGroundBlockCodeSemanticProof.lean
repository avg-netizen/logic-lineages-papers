module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeTargets
public import LogicLineages.OrdinalComparison.OneUnitCodeProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodeProof
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof
open SyntaxCode ContextInsertionCode

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

private theorem index_step (depth count i : Nat) :
    indexCode (depth+1) count (i+1) = indexCode depth count i+1 := by
  by_cases h : i<depth <;> simp [indexCode,h] <;> omega

private def mapRaw (depth count : Nat) : Raw → Raw
  | .var i => .var (indexCode depth count i)
  | .zero => .zero
  | .succ => .succ
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .app f a => .app (mapRaw depth count f) (mapRaw depth count a)
  | .lam σ b => .lam σ (mapRaw (depth+1) count b)

private theorem raw_correct (depth count : Nat) (t : Raw) :
    sourceCode depth count (code t) = code (mapRaw depth count t) := by
  induction t generalizing depth with
  | var i => rw [code,sourceCode];simp [mapRaw,code]
  | zero => rw [code,sourceCode];simp [mapRaw,code]
  | succ => rw [code,sourceCode];simp [mapRaw,code]
  | caseC τ => rw [code,sourceCode];simp [mod_tag _ 3 (by decide),mapRaw,code]
  | recC τ => rw [code,sourceCode];simp [mod_tag _ 4 (by decide),mapRaw,code]
  | app f a ihf iha =>
    rw [code,sourceCode]
    simp [mod_tag _ 5 (by decide),div_tag _ 5 (by decide),ihf,iha,mapRaw,code]
  | lam σ b ih =>
    rw [code,sourceCode]
    simp [mod_tag _ 6 (by decide),div_tag _ 6 (by decide),ih,mapRaw,code]

private theorem lift_index {Γ Δ τ} {depth count : Nat} (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x)) :
    ∀ {σ} (x : Variable (τ::Γ) σ), SourceTypedPorts.variableIndex (Renaming.lift r x) =
      indexCode (depth+1) count (SourceTypedPorts.variableIndex x) := by
  intro σ x
  cases x with
  | here => simp [Renaming.lift,SourceTypedPorts.variableIndex,indexCode]
  | there x =>
    change SourceTypedPorts.variableIndex (r x)+1 = indexCode (depth+1) count (SourceTypedPorts.variableIndex x+1)
    rw [h,index_step]

private theorem erase_rename {Γ Δ τ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (t : OriginalTerm Γ τ) : erase (t.rename r) = mapRaw depth count (erase t) := by
  induction t generalizing Δ depth with
  | var x => simp [Source.Term.rename,erase,mapRaw,h]
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a ihf iha => simp only [Source.Term.rename,erase,mapRaw,ihf _ r h,iha _ r h]
  | lam b ih =>
    simp only [Source.Term.rename,erase,mapRaw]
    rw [ih (depth+1) (Renaming.lift r) (lift_index r h)]
  | ranked s _ => nomatch s


private theorem source_correct {Γ Δ τ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (t : OriginalTerm Γ τ) : sourceCode depth count (encodeTerm t) = encodeTerm (t.rename r) := by
  rw [encodeTerm,raw_correct,encodeTerm,erase_rename _ _ _ h t]

private theorem probe_correct {Γ τ} (t : OriginalTerm Γ τ) (x : Variable Γ .ground) :
    probeCode (typeCode τ) (encodeTerm t) (SourceTypedPorts.variableIndex x) =
      encodeTerm (AbsoluteObserver.probe t x) := by
  unfold probeCode
  rw [OneUnitCode.Proof.exactLiteralSyntax.1 Γ τ t]
  rfl

theorem exactProbeCodes : Targets.ExactProbeCodes := by
  constructor
  · intro Γ τ t
    have h := ContextInsertionCode.Proof.exactSourceInsertion [] [.ground,.ground] Γ τ t
    change sourceCode 0 2 (encodeTerm t) = encodeTerm (t.rename (AbsoluteObserver.shiftTwo Γ)) at h
    unfold originalProbeCode
    rw [h]
    exact probe_correct _ .here
  · intro Γ hΓ τ t
    have hc := GroundClosingCode.Proof.closedExact Γ τ (AbsoluteObserver.closingMap hΓ) t
    change GroundClosingCode.closeCode 0 (encodeTerm t) = encodeTerm (AbsoluteObserver.close hΓ t) at hc
    have he := source_correct 0 (Γ.length+2) (AbsoluteObserver.fromEmpty (.ground::.ground::Γ))
      (fun x => nomatch x) (AbsoluteObserver.close hΓ t)
    unfold closedProbeCode
    rw [hc,he]
    exact probe_correct _ (.there .here)

theorem exactGroundBlock : Targets.ExactGroundBlock := by
  intro Γ hΓ τ t
  have hc := (OneUnitCode.Proof.exactLiteralSyntax.2.2 τ ⟨0,0,false⟩).1
  change OneUnitCode.coefficientCode (typeCode τ) = AbsoluteObserver.factor τ at hc
  unfold buildCode
  rw [exactProbeCodes.1 Γ τ t,exactProbeCodes.2 Γ hΓ τ t,hc]
  rfl
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof
