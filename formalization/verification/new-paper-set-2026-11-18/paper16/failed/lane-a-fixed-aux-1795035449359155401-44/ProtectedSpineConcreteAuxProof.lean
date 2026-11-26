import LogicLineages.PersistentMarking.ProtectedSpineConcreteInputProof
import LogicLineages.PersistentMarking.ProtectedSpineTableProof

namespace LogicLineages.PersistentMarking.ProtectedSpineConcreteAuxProof
open Spine NameBridge DecisionPorts FiniteDomainSchema FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreterCore ProtectedSpineInterpreter
open ProtectedSpineFixedApplicationTargets ProtectedSpineConcreteInputProof ProtectedSpineBoundTargets
open MarkedConstructorTargets (PrefixClosed)

theorem empty (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (q : Expr) (vs : Args) (types : List Ty)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (hv : BoundImages E H vs types)
    (ht : Typed (BoundContext.prefix types EmptyContext) q q.type) (hq : Covered E H q) :
    helperAux S E H M Γ q .nil vs q.type = concreteOutput S E H M Γ q.type (applyAux q .nil vs) := by
  have h := ProtectedSpineBoundSubstitutionProof.exact_BoundSubstitution S E H M vs types [] q q.type
    hc hm hv ht hq
  have he := h.value Γ ⟨[],closedCodes S E H M Γ vs⟩ ⟨[],[]⟩
    (boundValid S E H M Γ vs types hc hm hw hv) (emptyValid E Γ hw) (boundRelation S E H M Γ vs)
  have hcode := HereditaryEncodingCongruenceProof.congruence E q.type Γ _ _ he
  rw [applyAux]
  exact hcode

theorem consEq (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (q a : Expr) (args vs : Args) (τ : Ty) :
    helperAux S E H M Γ q (.cons a args) vs τ =
      (evaluate S E H M q).nonempty Γ [] (closedCodes S E H M Γ vs) vs.length a.type
        (codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩) (domainTypes args)
        ((closedCodes S E H M Γ args).map Prod.snd) τ := rfl

theorem typingLength (vs : Args) (types : List Ty) (h : BaseTyped EmptyContext vs types) :
    vs.length = types.length := by
  cases vs with
  | nil => cases h; rfl
  | cons q qs =>
    cases h with
    | cons hq hqs =>
      have ih := typingLength qs _ hqs
      simp only [Args.length,List.length_cons]
      omega
termination_by sizeOf vs

theorem boundBlocked (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (α : Ty) (i : Nat) (a : Expr) (args vs : Args) (types : List Ty) (τ : Ty)
    (hv : BaseTyped EmptyContext vs types) (h : BoundContext.prefix types EmptyContext i = some α) :
    helperAux S E H M Γ (.bound α i) (.cons a args) vs τ =
      concreteOutput S E H M Γ τ (applyAux (.bound α i) (.cons a args) vs) := by
  rw [ProtectedSpineBoundSyntaxProof.emptyPrefix] at h
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp h
  have hip : i < vs.length := typingLength vs types hv ▸ hi
  rw [consEq,applyAux]
  change (if protectedLookup vs.length i then _ else _) = StructuralActions.bottom E τ Γ
  simp [protectedLookup,hip]

theorem freeBlocked (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (α : Ty) (x : Nat) (a : Expr) (args vs : Args) (τ : Ty)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (ht : CallTyped EmptyContext α (.cons a args) τ)
    (hCov : ArgsCovered E H (.cons a args)) :
    helperAux S E H M Γ (.free α x) (.cons a args) vs τ =
      concreteOutput S E H M Γ τ (applyAux (.free α x) (.cons a args) vs) := by
  have hpre := fullPrefix α a args τ ht
  have htup := (codeValid S E H M Γ (.cons a args) (domainTypes (.cons a args)) hc hm hw
    ⟨(argumentTypes α (.cons a args) τ ht).1,hCov⟩).2
  have hv := (HereditaryEncodeDecodeProof.encodeDecode E α Γ (literal E α x) hw
    (MarkedConstructorLiteralProof.literalValid E α Γ x)).2
  have he := (hv Γ hw (DecisionPortsProof.extensionRefl Γ)).2.2 _ τ hpre _ htup
  rw [applyAux]
  change variableCall E α Γ (literalCode E Γ α x) (domainTypes (.cons a args))
    ((closedCodes S E H M Γ (.cons a args)).map Prod.snd) τ = StructuralActions.bottom E τ Γ
  unfold variableCall
  rw [if_pos ⟨MarkedConstructorTupleProof.prefixResidual hpre,htup.1⟩]
  exact he

theorem lambdaStep (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (α : Ty) (body a : Expr) (args vs : Args) (τ : Ty)
    (ha : a.type = α) (ht : CallTyped EmptyContext body.type args τ) :
    helperAux S E H M Γ (.lam α body) (.cons a args) vs τ =
      helperAux S E H M Γ body args (.cons a vs) τ := by
  rw [consEq]
  change lambdaCall E α body.type (evaluate S E H M body) Γ [] (closedCodes S E H M Γ vs)
    vs.length a.type (codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩)
    (domainTypes args) ((closedCodes S E H M Γ args).map Prod.snd) τ = _
  unfold lambdaCall
  rw [if_pos ha]
  cases args with
  | nil =>
    cases ht
    change (if body.type = body.type then _ else _) = _
    rw [if_pos rfl]
    change codeAt E body.type (evaluate S E H M body) Γ
        ⟨[], (α,codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩)::closedCodes S E H M Γ vs⟩ =
      codeAt E body.type (evaluate S E H M body) Γ
        ⟨[],(a.type,codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩)::closedCodes S E H M Γ vs⟩
    rw [ha]
  | cons b bs =>
    rw [consEq]
    change (evaluate S E H M body).nonempty Γ []
      ((α,codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩)::closedCodes S E H M Γ vs) (vs.length+1)
      b.type (codeAt E b.type (evaluate S E H M b) Γ ⟨[],[]⟩)
      (domainTypes bs) ((closedCodes S E H M Γ bs).map Prod.snd) τ =
      (evaluate S E H M body).nonempty Γ []
        ((a.type,codeAt E a.type (evaluate S E H M a) Γ ⟨[],[]⟩)::closedCodes S E H M Γ vs) (1+vs.length)
        b.type (codeAt E b.type (evaluate S E H M b) Γ ⟨[],[]⟩)
        (domainTypes bs) ((closedCodes S E H M Γ bs).map Prod.snd) τ
    rw [ha,Nat.add_comm vs.length 1]

end LogicLineages.PersistentMarking.ProtectedSpineConcreteAuxProof
