module
public import LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingBranchesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation StructuralRenaming LambdaSpineActions LambdaObservationMatching StructuralRenamingSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem variablePull {Γ Δ : List Ty} {τ : Ty} (r : Renaming Γ Δ) (v : Variable Γ τ) :
    OriginalSpineActionsProof.variableAction (I := I) (r v)=pullAction r (OriginalSpineActionsProof.variableAction v) := by
  apply actionExt <;> rfl

theorem ordinaryPull {Γ Δ : List Ty} (r : Renaming Γ Δ) (f : HeadIndex I)
    (base : ArgumentActions I Γ (headArguments arity f.val)) :
    FunctionalSpineActionsProof.ordinaryAction f (fun i => pullAction r (base i))=
      pullAction r (FunctionalSpineActionsProof.ordinaryAction f base) := by
  apply actionExt <;> rfl

theorem markedPull {Γ Δ : List Ty} (r : Renaming Γ Δ) (f : HeadIndex I) (τ : TypedExtraDownsets.TypeIndex I)
    (base : ArgumentActions I Γ (headArguments arity f.val)) (types : List Ty)
    (ht : ∀ υ ∈ types,υ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ types) :
    FunctionalSpineActionsProof.markedAction f τ (fun i => pullAction r (base i)) types ht (fun i => pullAction r (extras i))=
      pullAction r (FunctionalSpineActionsProof.markedAction f τ base types ht extras) := by
  apply actionExt <;> rfl

theorem rawPull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Δ P) :
    lambdaRaw (renameTerm body r.lift) (pullAction r.lift A) M P ρ = lambdaRaw body A M P (reindex r ρ) := by
  apply Prod.ext
  · funext Q
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext o
        exact matchPull r body A M Q.val (restrict Q.property ρ) false (observationBody o)
      · funext o
        exact matchPull r body A M Q.val (restrict Q.property ρ) true (observationBody o)
  · funext Q s args
    exact nonemptyPull r A M Q.val (restrict Q.property ρ) (fun {_} _ => false) s.val.1 s.val.2 args _ _

theorem valuePull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Δ P) :
    LambdaSpineActionsProof.lambdaValue (renameTerm body r.lift) (pullAction r.lift A) M P ρ=
      LambdaSpineActionsProof.lambdaValue body A M P (reindex r ρ) := by
  apply RecursiveNaturalDomainsProof.layerViewInjective I (.arrow σ υ) P
  apply Subtype.ext
  exact (LambdaSpineActionsProof.valueLayer (renameTerm body r.lift) (pullAction r.lift A) M P ρ).trans
    ((rawPull r body A M P ρ).trans (LambdaSpineActionsProof.valueLayer body A M P (reindex r ρ)).symm)

theorem lambdaPull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) :
    LambdaSpineActionsProof.lambdaAction (renameTerm body r.lift) (pullAction r.lift A)=
      pullAction r (LambdaSpineActionsProof.lambdaAction body A) := by
  apply actionExt
  · funext M P ρ
    exact valuePull r body A M P ρ
  · funext M P ρ mask types τ args h
    change lambdaScan (pullAction r.lift A) (LambdaSpineActionsProof.lambdaValue (renameTerm body r.lift) (pullAction r.lift A)) M P ρ mask types τ args h =
      lambdaScan A (LambdaSpineActionsProof.lambdaValue body A) M P (reindex r ρ) (pullMask r mask) types τ args h
    by_cases hn : types=[]
    · simp only [lambdaScan,dif_pos hn]
      exact congrArg (castValue _) (valuePull r body A M P ρ)
    · simp only [lambdaScan,dif_neg hn]
      exact nonemptyPull r A M P ρ mask types τ args h hn

end LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingBranchesProof
