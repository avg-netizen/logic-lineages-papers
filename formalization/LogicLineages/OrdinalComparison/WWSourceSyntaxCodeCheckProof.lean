module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckPrimitiveProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof

private theorem check_mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem check_div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

theorem checkCodeExact : Targets.CheckCodeExact := by
  intro Γ r
  induction r generalizing Γ with
  | var i => rw [code,check]; simp [inferRaw]
  | zero => rw [code,check]; simp [inferRaw]
  | succ => rw [code,check]; simp [inferRaw]
  | caseC τ => rw [code,check]; simp [check_mod_tag τ 3 (by omega),check_div_tag τ 3 (by omega),inferRaw]
  | recC τ => rw [code,check]; simp [check_mod_tag τ 4 (by omega),check_div_tag τ 4 (by omega),inferRaw]
  | app f a hf ha =>
      rw [code,check]
      simp [check_mod_tag _ 5 (by omega),check_div_tag _ 5 (by omega),Nat.unpair_pair,hf,ha,inferRaw]
  | lam σ b hb =>
      rw [code,check]
      simp [check_mod_tag _ 6 (by omega),check_div_tag _ 6 (by omega),Nat.unpair_pair,hb,inferRaw]

theorem checkParserExact : Targets.CheckParserExact := by
  intro Γ n
  induction n using Nat.strong_induction_on generalizing Γ with
  | h n ih =>
      rw [check,decode]
      have ht : n%8=0 ∨ n%8=1 ∨ n%8=2 ∨ n%8=3 ∨ n%8=4 ∨ n%8=5 ∨ n%8=6 ∨ n%8=7 := by omega
      rcases ht with ht|ht|ht|ht|ht|ht|ht|ht
      · simp [ht,inferRaw]
      · by_cases hz : n/8=0 <;> simp [ht,hz,inferRaw]
      · by_cases hz : n/8=0 <;> simp [ht,hz,inferRaw]
      · simp [ht,inferRaw]
      · simp [ht,inferRaw]
      · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
        have hl := (Nat.unpair_left_le (n/8)).trans_lt hd
        have hr := (Nat.unpair_right_le (n/8)).trans_lt hd
        simp only [show n%8=5 from ht]
        simp only [show ¬(5:Nat)=0 from by decide,show ¬(5:Nat)=1 from by decide,
          show ¬(5:Nat)=2 from by decide,show ¬(5:Nat)=3 from by decide,
          show ¬(5:Nat)=4 from by decide,if_false,if_true,or_true,true_or]
        rw [ih _ hl Γ,ih _ hr Γ]
        cases hf : decode (n/8).unpair.1 <;> cases ha : decode (n/8).unpair.2 <;>
          simp [hf,ha,appResult,inferRaw]
      · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
        have hr := (Nat.unpair_right_le (n/8)).trans_lt hd
        simp only [show n%8=6 from ht]
        simp only [show ¬(6:Nat)=0 from by decide,show ¬(6:Nat)=1 from by decide,
          show ¬(6:Nat)=2 from by decide,show ¬(6:Nat)=3 from by decide,
          show ¬(6:Nat)=4 from by decide,show ¬(6:Nat)=5 from by decide,
          if_false,if_true,or_true,true_or]
        rw [ih _ hr ((n/8).unpair.1::Γ)]
        cases hb : decode (n/8).unpair.2 <;> simp [hb,inferRaw]
      · simp [ht]

private theorem typeCode_injective : Function.Injective typeCode := by
  intro σ τ h
  exact (StatementChecks.typeDecodeEncode σ).symm.trans
    ((congrArg decodeType h).trans (StatementChecks.typeDecodeEncode τ))

private theorem variableLookup {Γ : List Ty} {τ : Ty} (v : Variable Γ τ) :
    (Γ.map typeCode)[SourceTypedPorts.variableIndex v]? = some (typeCode τ) := by
  induction v with
  | here => simp [SourceTypedPorts.variableIndex]
  | there v ih => simpa [SourceTypedPorts.variableIndex] using ih

private theorem variableFromLookup (Γ : List Ty) (τ : Ty) (i : Nat)
    (h : (Γ.map typeCode)[i]? = some (typeCode τ)) :
    ∃ v : Variable Γ τ, SourceTypedPorts.variableIndex v = i := by
  induction Γ generalizing i with
  | nil => simp at h
  | cons σ Γ ih =>
      cases i with
      | zero =>
          have he : typeCode σ = typeCode τ := by simpa using h
          have he := typeCode_injective he
          subst τ
          exact ⟨.here,rfl⟩
      | succ i =>
          have hh : (Γ.map typeCode)[i]? = some (typeCode τ) := by simpa using h
          obtain ⟨v,hv⟩ := ih i hh
          exact ⟨.there v,by simp [SourceTypedPorts.variableIndex,hv]⟩

private theorem typedSound {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) :
    inferRaw (Γ.map typeCode) (erase t) = some (typeCode τ) := by
  induction t with
  | var v => exact variableLookup v
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a hf ha => simp [erase,inferRaw,hf,ha,appResult,typeCode,arrowCode]
  | lam b hb =>
      simp only [List.map_cons] at hb
      simp [erase,inferRaw,hb,typeCode]
  | ranked s _ _ => cases s

private theorem rawComplete (r : Raw) (Γ : List Ty) (τ : Ty)
    (h : inferRaw (Γ.map typeCode) r = some (typeCode τ)) :
    ∃ t : OriginalTerm Γ τ, erase t = r := by
  induction r generalizing Γ τ with
  | var i =>
      obtain ⟨v,hv⟩ := variableFromLookup Γ τ i h
      exact ⟨.var v,by simp [erase,hv]⟩
  | zero =>
      have he : typeCode Ty.ground = typeCode τ := by simpa [inferRaw,typeCode] using h
      have he := typeCode_injective he
      subst τ
      exact ⟨.zeroC,rfl⟩
  | succ =>
      have he : typeCode (.arrow .ground .ground) = typeCode τ := by simpa [inferRaw,typeCode] using h
      have he := typeCode_injective he
      subst τ
      exact ⟨.succC,rfl⟩
  | caseC a =>
      have he : typeCode (Ty.caseType (decodeType a)) = typeCode τ := by
        simpa [inferRaw,typeCode,Ty.caseType,caseCode,StatementChecks.typeEncodeDecode a] using h
      have he := typeCode_injective he
      subst τ
      exact ⟨.caseC (decodeType a),by simp [erase,StatementChecks.typeEncodeDecode a]⟩
  | recC a =>
      have he : typeCode (Ty.recType (decodeType a)) = typeCode τ := by
        simpa [inferRaw,typeCode,Ty.recType,recCode,StatementChecks.typeEncodeDecode a] using h
      have he := typeCode_injective he
      subst τ
      exact ⟨.recC (decodeType a),by simp [erase,StatementChecks.typeEncodeDecode a]⟩
  | app f a ihf iha =>
      cases hf : inferRaw (Γ.map typeCode) f with
      | none => simp [inferRaw,appResult,hf] at h
      | some tf =>
        cases ha : inferRaw (Γ.map typeCode) a with
        | none => simp [inferRaw,appResult,hf,ha] at h
        | some ta =>
          by_cases hz : tf=0
          · simp [inferRaw,appResult,hf,ha,hz] at h
          by_cases hd : (tf-1).unpair.1=ta
          · have hc : (tf-1).unpair.2=typeCode τ := by
              simpa [inferRaw,appResult,hf,ha,hz,hd] using h
            have he : arrowCode ta (typeCode τ)=tf := by
              rw [arrowCode,←hd,←hc,Nat.pair_unpair]
              omega
            have hft : inferRaw (Γ.map typeCode) f = some (typeCode (.arrow (decodeType ta) τ)) := by
              simpa [typeCode,StatementChecks.typeEncodeDecode ta,he] using hf
            have hat : inferRaw (Γ.map typeCode) a = some (typeCode (decodeType ta)) := by
              simpa [StatementChecks.typeEncodeDecode ta] using ha
            obtain ⟨f',hf'⟩ := ihf Γ _ hft
            obtain ⟨a',ha'⟩ := iha Γ _ hat
            exact ⟨.app f' a',by simp [erase,hf',ha']⟩
          · simp [inferRaw,appResult,hf,ha,hz,hd] at h
  | lam σ b ih =>
      cases hb : inferRaw (σ::Γ.map typeCode) b with
      | none => simp [inferRaw,hb] at h
      | some tb =>
          have hc : arrowCode σ tb=typeCode τ := by simpa [inferRaw,hb] using h
          have he : typeCode (.arrow (decodeType σ) (decodeType tb))=typeCode τ := by
            simpa [typeCode,StatementChecks.typeEncodeDecode σ,StatementChecks.typeEncodeDecode tb] using hc
          have he := typeCode_injective he
          subst τ
          have hbt : inferRaw (((decodeType σ)::Γ).map typeCode) b = some (typeCode (decodeType tb)) := by
            simpa [List.map_cons,StatementChecks.typeEncodeDecode σ,StatementChecks.typeEncodeDecode tb] using hb
          obtain ⟨b',hb'⟩ := ih (decodeType σ::Γ) (decodeType tb) hbt
          exact ⟨.lam b',by simp [erase,hb',StatementChecks.typeEncodeDecode σ]⟩

theorem typedRawExact : Targets.TypedRawExact := by
  intro Γ τ r
  constructor
  · exact rawComplete r Γ τ
  · rintro ⟨t,rfl⟩
    exact typedSound t

theorem typedCheckExact : Targets.TypedCheckExact := by
  intro Γ τ n
  constructor
  · intro h
    rw [checkParserExact] at h
    cases hd : decode n with
    | none => simp [hd] at h
    | some r =>
        have hr : inferRaw (Γ.map typeCode) r = some (typeCode τ) := by simpa [hd] using h
        obtain ⟨t,ht⟩ := (typedRawExact Γ τ r).mp hr
        exact ⟨t,by rw [encodeTerm,ht]; exact StatementChecks.encodeDecode n r hd⟩
  · rintro ⟨t,rfl⟩
    rw [encodeTerm,checkCodeExact]
    exact typedSound t
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof
