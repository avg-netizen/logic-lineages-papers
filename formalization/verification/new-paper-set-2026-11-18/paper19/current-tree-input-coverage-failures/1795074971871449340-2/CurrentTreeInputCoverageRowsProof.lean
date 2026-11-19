module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageTypedProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage

open LogicLineages.OrdinalComparison.Source GroundEquivalence RawSourceDAG

private theorem modTag (x a : Nat) (ha : a < 8) : (8*x+a)%8 = a := by omega
private theorem divTag (x a : Nat) (ha : a < 8) : (8*x+a)/8 = x := by omega

private theorem rowVar (Γ Δ : List Nat) (i : Nat) :
    rows Γ Δ (8*i) = [(Δ,(SyntaxCode.check (Δ++Γ) (8*i)).getD 0,0,[i])] := by
  rw [rows]
  simp [show (8*i)%8 = 0 by omega, show (8*i)/8 = i by omega]

private theorem rowZero (Γ Δ : List Nat) :
    rows Γ Δ 1 = [(Δ,(SyntaxCode.check (Δ++Γ) 1).getD 0,3,[])] := by
  rw [rows] <;> rfl

private theorem rowSucc (Γ Δ : List Nat) :
    rows Γ Δ 2 = [(Δ,(SyntaxCode.check (Δ++Γ) 2).getD 0,4,[])] := by
  rw [rows] <;> rfl

private theorem rowCase (Γ Δ : List Nat) (i : Nat) :
    rows Γ Δ (8*i+3) = [(Δ,(SyntaxCode.check (Δ++Γ) (8*i+3)).getD 0,5,[i])] := by
  rw [rows]
  simp [modTag i 3 (by decide),divTag i 3 (by decide)]

private theorem rowRec (Γ Δ : List Nat) (i : Nat) :
    rows Γ Δ (8*i+4) = [(Δ,(SyntaxCode.check (Δ++Γ) (8*i+4)).getD 0,6,[i])] := by
  rw [rows]
  simp [modTag i 4 (by decide),divTag i 4 (by decide)]

private theorem rowApp (Γ Δ : List Nat) (f a : Nat) :
    let n := 8*Nat.pair f a+5
    rows Γ Δ n =
      (Δ,(SyntaxCode.check (Δ++Γ) n).getD 0,1,
        [(SyntaxCode.check (Δ++Γ) a).getD 0,(rows Γ Δ a).length,0]) ::
      (rows Γ Δ a ++ rows Γ Δ f) := by
  dsimp only
  rw [rows]
  simp [modTag _ 5 (by decide),divTag _ 5 (by decide),Nat.unpair_pair]

private theorem rowLam (Γ Δ : List Nat) (σ b : Nat) :
    let n := 8*Nat.pair σ b+6
    rows Γ Δ n =
      (Δ,(SyntaxCode.check (Δ++Γ) n).getD 0,2,
        [σ,(SyntaxCode.check ((σ::Δ)++Γ) b).getD 0,0]) ::
      rows Γ (σ::Δ) b := by
  dsimp only
  rw [rows]
  simp [modTag _ 6 (by decide),divTag _ 6 (by decide),Nat.unpair_pair]

private theorem typedCheck {Ξ : List Ty} {τ : Ty} (t : OriginalTerm Ξ τ)
    (Γ Δ : List Ty) (h : Δ++Γ = Ξ) :
    (SyntaxCode.check (Δ.map SyntaxCode.typeCode ++ Γ.map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm t)).getD 0 = SyntaxCode.typeCode τ := by
  subst Ξ
  have hh := (SyntaxCode.StatementChecks.typedCheckExact (Δ++Γ) τ (SyntaxCode.encodeTerm t)).mpr ⟨t,rfl⟩
  rw [List.map_append] at hh
  rw [hh] <;> rfl

private theorem indexTransfer {Ξ K : List Ty} {σ : Ty} (h : K = Ξ) (x : Variable Ξ σ) :
    variableIndex (h.symm ▸ x) = SourceTypedPorts.variableIndex x := by
  subst Ξ
  induction x with
  | here => rfl
  | there x ih => exact congrArg (·+1) ih

private def rowsOf {Ξ : List Ty} {τ : Ty} (Γ Δ : List Ty) (t : OriginalTerm Ξ τ) : List Node :=
  rows (Γ.map SyntaxCode.typeCode) (Δ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t)

private theorem rowsIn {Ξ : List Ty} {τ : Ty} (t : OriginalTerm Ξ τ)
    (Γ Δ : List Ty) (h : Δ++Γ = Ξ) {ss : List Spec} (d : DAG Γ ss) :
    let r := buildIn t Γ Δ h d
    encodeGraph r.graph = rowsOf Γ Δ t ++ encodeGraph d ∧
    ∀ (s : Spec) (ref : Ref ss s),
      referenceIndex (r.keep ref) = (rowsOf Γ Δ t).length + referenceIndex ref := by
  induction t generalizing Γ Δ ss with
  | var x =>
    have hc := typedCheck (.var x) Γ Δ h
    constructor
    · simp only [buildIn,encodeGraph,node,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,
        SyntaxCode.code,rowVar,List.singleton_append]
      rw [indexTransfer h]
      exact congrArg (fun u => ((Δ.map SyntaxCode.typeCode,u,0,[SourceTypedPorts.variableIndex x]) : Node) ::
        encodeGraph d) hc.symm
    · intro s ref
      simp [buildIn,referenceIndex,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
        rowVar,Nat.add_comm]
  | zeroC =>
    have hc := typedCheck (Term.zeroC : OriginalTerm _ .ground) Γ Δ h
    constructor
    · simp only [buildIn,encodeGraph,node,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,
        SyntaxCode.code,rowZero,List.singleton_append]
      exact congrArg (fun u => ((Δ.map SyntaxCode.typeCode,u,3,[]) : Node) :: encodeGraph d) hc.symm
    · intro s ref
      simp [buildIn,referenceIndex,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
        rowZero,Nat.add_comm]
  | succC =>
    have hc := typedCheck (Term.succC : OriginalTerm _ (.arrow .ground .ground)) Γ Δ h
    constructor
    · simp only [buildIn,encodeGraph,node,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,
        SyntaxCode.code,rowSucc,List.singleton_append]
      exact congrArg (fun u => ((Δ.map SyntaxCode.typeCode,u,4,[]) : Node) :: encodeGraph d) hc.symm
    · intro s ref
      simp [buildIn,referenceIndex,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
        rowSucc,Nat.add_comm]
  | caseC σ =>
    have hc := typedCheck (Term.caseC σ : OriginalTerm _ σ.caseType) Γ Δ h
    constructor
    · simp only [buildIn,encodeGraph,node,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,
        SyntaxCode.code,rowCase,List.singleton_append]
      exact congrArg (fun u => ((Δ.map SyntaxCode.typeCode,u,5,[SyntaxCode.typeCode σ]) : Node) ::
        encodeGraph d) hc.symm
    · intro s ref
      simp [buildIn,referenceIndex,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
        rowCase,Nat.add_comm]
  | recC σ =>
    have hc := typedCheck (Term.recC σ : OriginalTerm _ σ.recType) Γ Δ h
    constructor
    · simp only [buildIn,encodeGraph,node,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,
        SyntaxCode.code,rowRec,List.singleton_append]
      exact congrArg (fun u => ((Δ.map SyntaxCode.typeCode,u,6,[SyntaxCode.typeCode σ]) : Node) ::
        encodeGraph d) hc.symm
    · intro s ref
      simp [buildIn,referenceIndex,rowsOf,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
        rowRec,Nat.add_comm]
  | @app Ξ σ τ f a ihf iha =>
    let F := buildIn f Γ Δ h d
    let A := buildIn a Γ Δ h F.graph
    have hf := ihf Γ Δ h d
    have ha := iha Γ Δ h F.graph
    have checkR := typedCheck (Term.app f a) Γ Δ h
    have checkA := typedCheck a Γ Δ h
    have hrows : rowsOf Γ Δ (Term.app f a) =
        (Δ.map SyntaxCode.typeCode,SyntaxCode.typeCode τ,1,
          [SyntaxCode.typeCode σ,(rowsOf Γ Δ a).length,0]) ::
        (rowsOf Γ Δ a ++ rowsOf Γ Δ f) := by
      unfold rowsOf
      change rows _ _ (8*Nat.pair (SyntaxCode.encodeTerm f) (SyntaxCode.encodeTerm a)+5) = _
      rw [rowApp]
      rw [show 8*Nat.pair (SyntaxCode.encodeTerm f) (SyntaxCode.encodeTerm a)+5 =
        SyntaxCode.encodeTerm (Term.app f a) from rfl, checkR,checkA]
    constructor
    · rw [hrows]
      simp only [buildIn,encodeGraph,node,referenceIndex,List.cons_append]
      change (_ :: encodeGraph A.graph) = _
      rw [ha.1,hf.1,ha.2,referenceIndex,Nat.add_zero,List.append_assoc]
    · intro s ref
      rw [hrows]
      simp only [buildIn,referenceIndex,List.length_cons,List.length_append]
      change referenceIndex (A.keep (F.keep ref)) + 1 =
        ((rowsOf Γ Δ a).length + (rowsOf Γ Δ f).length + 1) + referenceIndex ref
      rw [ha.2,hf.2]
      omega
  | @lam Ξ σ τ b ih =>
    let B := buildIn b Γ (σ :: Δ) (congrArg (List.cons σ) h) d
    have hb := ih Γ (σ :: Δ) (congrArg (List.cons σ) h) d
    have checkR := typedCheck (Term.lam b) Γ Δ h
    have checkB := typedCheck b Γ (σ :: Δ) (congrArg (List.cons σ) h)
    have hrows : rowsOf Γ Δ (Term.lam b) =
        (Δ.map SyntaxCode.typeCode,SyntaxCode.typeCode (.arrow σ τ),2,
          [SyntaxCode.typeCode σ,SyntaxCode.typeCode τ,0]) :: rowsOf Γ (σ::Δ) b := by
      unfold rowsOf
      change rows _ _ (8*Nat.pair (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm b)+6) = _
      rw [rowLam]
      rw [show 8*Nat.pair (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm b)+6 =
        SyntaxCode.encodeTerm (Term.lam b) from rfl, checkR]
      simp only [List.map_cons] at checkB
      rw [checkB] <;> rfl
    constructor
    · rw [hrows]
      simp only [buildIn,encodeGraph,node,referenceIndex,List.cons_append]
      exact congrArg (fun as => ((Δ.map SyntaxCode.typeCode,
          SyntaxCode.typeCode (.arrow σ τ),2,[SyntaxCode.typeCode σ,SyntaxCode.typeCode τ,0]) : Node) ::
          as) hb.1
    · intro s ref
      rw [hrows]
      simp only [buildIn,referenceIndex,List.length_cons]
      change referenceIndex (B.keep ref) + 1 = ((rowsOf Γ (σ::Δ) b).length + 1) + referenceIndex ref
      rw [hb.2]
      omega
  | ranked s _ _ => nomatch s

theorem treeCodes : CurrentTreeInputCoverageTargets.ActualTreeCodes := by
  intro Γ τ t
  refine ⟨inputTerm t,?_,?_⟩
  · have hc := (SyntaxCode.StatementChecks.typedCheckExact Γ τ (SyntaxCode.encodeTerm t)).mpr ⟨t,rfl⟩
    unfold compile
    rw [hc]
    have h := (rowsIn t Γ [] rfl DAG.nil).1
    change encodeGraph (build t (Δ:=[]) DAG.nil).graph =
      rows (Γ.map SyntaxCode.typeCode) [] (SyntaxCode.encodeTerm t) ++ [] at h
    rw [List.append_nil] at h
    change some (_,rows (Γ.map SyntaxCode.typeCode) [] (SyntaxCode.encodeTerm t),0,_) =
      some (_,encodeGraph (build t (Δ:=[]) DAG.nil).graph,0,_)
    rw [h]
  · rw [CurrentTreeCode.exactExpansion Γ τ (input t),inputTerm]

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage
