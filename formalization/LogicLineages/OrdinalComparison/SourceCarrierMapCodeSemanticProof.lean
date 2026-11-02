module
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
public import LogicLineages.OrdinalComparison.SourceSubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Proof
open SyntaxCode GroundClosing

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

theorem rawExact : Targets.RawExact := by
  intro fresh depth t
  induction t generalizing depth with
  | var i =>
    rw [code,mapCode]
    simp only [Nat.mul_mod_right,Nat.mul_div_cancel_left i (by decide : 0<8),if_pos rfl]
    cases fresh <;> by_cases hi : i<depth <;> by_cases he : i=depth <;>
      simp [mapRaw,variableRaw,variableCode,hi,he,code]
  | zero => rw [code,mapCode]; simp [mapRaw,code]
  | succ => rw [code,mapCode]; simp [mapRaw,code]
  | caseC τ =>
    rw [code,mapCode]
    simp [mod_tag τ 3 (by omega),div_tag τ 3 (by omega),mapRaw,code]
  | recC τ =>
    rw [code,mapCode]
    simp [mod_tag τ 4 (by omega),div_tag τ 4 (by omega),mapRaw,code]
  | app f a ihf iha =>
    rw [code,mapCode]
    simp [mod_tag _ 5 (by omega),div_tag _ 5 (by omega),Nat.unpair_pair,ihf,iha,mapRaw,code]
  | lam σ b ih =>
    rw [code,mapCode]
    simp [mod_tag _ 6 (by omega),div_tag _ 6 (by omega),Nat.unpair_pair,ih,mapRaw,code]

private def shiftRaw : Raw → Raw
  | .var i => .var (i+1)
  | q => q

private theorem variable_step (fresh : Bool) (depth i : Nat) :
    variableRaw fresh (depth+1) (i+1) = shiftRaw (variableRaw fresh depth i) := by
  cases fresh <;> by_cases hi : i<depth <;> by_cases he : i=depth <;>
    simp [variableRaw,shiftRaw,hi,he] <;> congr 1 <;> omega

theorem compatible_lift {Γ Δ : List Ty} {τ : Ty} {fresh : Bool} {depth : Nat}
    {r : GroundMap Γ Δ} (h : Compatible fresh depth r) :
    Compatible fresh (depth+1) (@GroundMap.lift Γ Δ τ r) := by
  intro σ x
  cases x with
  | here => simp [GroundMap.lift,Image.source,erase,variableRaw,SourceTypedPorts.variableIndex]
  | there x =>
    have hx := congrArg shiftRaw (h x)
    change erase ((@GroundMap.lift Γ Δ τ r _ (.there x)).source) =
      variableRaw fresh (depth+1) (SourceTypedPorts.variableIndex x+1)
    calc
      erase ((@GroundMap.lift Γ Δ τ r _ (.there x)).source) = shiftRaw (erase (r x).source) := by
        cases he : r x <;> simp [GroundMap.lift,he,Image.weaken,Image.source,erase,
          SourceTypedPorts.variableIndex,shiftRaw]
      _ = shiftRaw (variableRaw fresh depth (SourceTypedPorts.variableIndex x)) := hx
      _ = variableRaw fresh (depth+1) (SourceTypedPorts.variableIndex x+1) :=
        (variable_step fresh depth (SourceTypedPorts.variableIndex x)).symm

theorem erase_substitute {Γ Δ : List Ty} {τ : Ty} (fresh : Bool) (depth : Nat)
    (r : GroundMap Γ Δ) (h : Compatible fresh depth r) (t : OriginalTerm Γ τ) :
    erase (t.substitute r.source) = mapRaw fresh depth (erase t) := by
  induction t generalizing Δ depth with
  | var x => exact h x
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a ihf iha =>
    simp only [Source.Term.substitute,erase,mapRaw,ihf _ r h,iha _ r h]
  | lam b ih =>
    simp only [Source.Term.substitute,← GroundClosingCode.Proof.source_lift,erase,mapRaw]
    rw [ih (depth+1) r.lift (compatible_lift h)]
  | ranked s _ => nomatch s

theorem typedExact : Targets.TypedExact := by
  intro Γ Δ τ fresh depth r h t
  rw [encodeTerm,rawExact,encodeTerm,erase_substitute fresh depth r h t]

theorem concreteExact : Targets.ConcreteExact := by
  constructor
  · intro Γ τ t
    apply typedExact (.ground :: Γ) Γ τ false 0 (GroundOperatorDischarge.groundMap Γ) _ t
    intro σ x
    cases x <;> simp [GroundOperatorDischarge.groundMap,Image.source,erase,variableRaw,
      SourceTypedPorts.variableIndex]
  · intro Γ σ τ t
    let r : GroundMap (σ :: Γ) (σ :: σ :: Γ) := fun x => .var (UnaryCarrier.renameTracked x)
    have hc : Compatible true 0 r := by
      intro υ x
      cases x <;> simp [r,UnaryCarrier.renameTracked,Image.source,erase,variableRaw,
        SourceTypedPorts.variableIndex]
    have ht := typedExact (σ :: Γ) (σ :: σ :: Γ) τ true 0 r hc t
    have hs : t.substitute r.source = t.rename UnaryCarrier.renameTracked :=
      SourceSubstitutionSupportProof.variableSubstitutionRenaming Empty Empty.elim
        (σ :: Γ) (σ :: σ :: Γ) τ t UnaryCarrier.renameTracked
    exact ht.trans (congrArg encodeTerm hs)

end LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Proof
