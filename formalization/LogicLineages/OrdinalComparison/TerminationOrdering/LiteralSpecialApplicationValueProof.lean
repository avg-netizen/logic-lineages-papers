module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation SourceConstructorIteration ActualOriginalApplication LiteralSpecialApplicationValue LambdaSpineActions ConfinedSubstitution SubstitutionEnvironmentSupport

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem maskLift {Γ : List Ty} {σ : Ty} {P : World I} (ρ : Environment I Γ P) (x : Value I σ P)
    (a b : Protected Γ) (hab : MaskAgreement ρ a b) : MaskAgreement (extend x ρ) (protectExtend a) (protectExtend b) := by
  intro τ v
  cases v with
  | here => exact Or.inl rfl
  | there v => exact hab v

theorem scannerMasks {Γ : List Ty} {σ : Ty} (q : MarkedTerm Symbol arity Γ σ) :
    ∀ (hq : Confined I q) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (a b : Protected Γ),
      MaskAgreement ρ a b → ∀ (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),
      scan ⟨q,hq⟩ M P ρ a types τ args h=scan ⟨q,hq⟩ M P ρ b types τ args h := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro hq M P ρ a b hab types τ args h
    change variableScan v M P ρ a types τ args h=variableScan v M P ρ b types τ args h
    by_cases hn : types=[]
    · simp only [variableScan,if_pos hn]
    · rcases hab v with he | hb
      · simp only [variableScan,he]
      · have hv := hb types τ args h hn
        cases ha : a v <;> cases hc : b v <;> simp [variableScan,hn,ha,hc,hv]
  | lam body ih =>
    intro hq M P ρ a b hab types τ args h
    change lambdaScan (buildTerm I body ⟨hq.1.2.2,hq.2⟩) _ M P ρ a types τ args h=
      lambdaScan (buildTerm I body ⟨hq.1.2.2,hq.2⟩) _ M P ρ b types τ args h
    by_cases hn : types=[]
    · simp only [lambdaScan,dif_pos hn]
    · cases types with
      | nil => exact False.elim (hn rfl)
      | cons α rest =>
        exact ih ⟨hq.1.2.2,hq.2⟩ M P _ _ _ (maskLift ρ _ a b hab) rest τ (tailValues args) (Ty.arrow.inj h).2
  | ordinary f base ih => intro hq M P ρ a b hab types τ args h; rfl
  | marked f output base ts extras ihb ihe => intro hq M P ρ a b hab types τ args h; rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem variableBottom {P : World I} {σ : Ty} (v : Variable (portTypes P.val++I.context) σ) :
    BottomApplications (LiteralVariableValueProof.variableValue (I := I) v) := by
  intro types τ args h hn
  rw [ActualLimitApplicationSupportProof.withSuffix _ types τ args h hn]
  unfold applyValue LiteralVariableValueProof.variableValue
  rw [RecursiveNaturalDomainsProof.layerViewFold]
  rfl

theorem scannerMaskAgreement : LiteralSpecialApplicationValueTargets.ScannerMaskAgreement := by
  intro Symbol inst arity I Γ σ q M P ρ a b hab types τ args h
  exact scannerMasks q.val q.property M P ρ a b hab types τ args h

theorem literalIdentityMasks : LiteralSpecialApplicationValueTargets.LiteralIdentityMasks := by
  intro Symbol inst arity I P σ q M a b types τ args h
  exact scannerMasks q.val q.property M P (identity I P) a b (fun {_} v => Or.inr (variableBottom v)) types τ args h

theorem identityRange {Γ : List Ty} : RangeConfined I (fun {τ} (v : Variable Γ τ) => MarkedTerm.var (Symbol := Symbol) (arity := arity) v) := by
  intro τ v ht
  exact ⟨ht,trivial⟩

theorem identityAgreement (M : Constructors I) {Γ : List Ty} (P : World I) (ρ : Environment I Γ P) :
    Agreement M (fun {_} v => .var v) identityRange ρ ρ := by
  intro τ v ht
  rfl

theorem specialSuccess : LiteralSpecialApplicationValueTargets.SpecialSuccess := by
  intro Symbol inst arity I above dec P types τ q args ha r hr heq
  have happ := ActualLimitApplicationProof.fullApplication Symbol inst arity I above dec _ _ q P (identity I P) types τ
    (argumentValues args ha (limit I above) P (identity I P)) rfl
  have hmask := literalIdentityMasks Symbol inst arity I P _ q (limit I above) (fun {_} _ => false) (fun {_} _ => true)
    types τ (argumentValues args ha (limit I above) P (identity I P)) rfl
  have hs := ActualOriginalApplicationProof.successInterpretation Symbol inst arity I above dec _ _ _ q
    (fun {_} v => .var v) identityRange types τ args ha rfl P (identity I P) (identity I P)
    (identityAgreement (limit I above) P (identity I P)) r hr heq
  exact happ.trans (hmask.trans hs.symm)

theorem specialFailure : LiteralSpecialApplicationValueTargets.SpecialFailure := by
  intro Symbol inst arity I above dec P types τ q args ha heq
  have happ := ActualLimitApplicationProof.fullApplication Symbol inst arity I above dec _ _ q P (identity I P) types τ
    (argumentValues args ha (limit I above) P (identity I P)) rfl
  have hmask := literalIdentityMasks Symbol inst arity I P _ q (limit I above) (fun {_} _ => false) (fun {_} _ => true)
    types τ (argumentValues args ha (limit I above) P (identity I P)) rfl
  have hf := ActualOriginalApplicationProof.failureBottom Symbol inst arity I above dec _ _ _ q
    (fun {_} v => .var v) identityRange types τ args ha rfl P (identity I P) (identity I P)
    (identityAgreement (limit I above) P (identity I P)) heq
  exact happ.trans (hmask.trans hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueProof
