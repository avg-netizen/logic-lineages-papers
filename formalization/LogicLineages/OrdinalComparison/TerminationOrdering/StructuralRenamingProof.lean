module
public import LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingBranchesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation StructuralRenaming LambdaSpineActions StructuralRenamingSupportProof StructuralRenamingBranchesProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem buildRename {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q) (Δ : List Ty) (r : Renaming Γ Δ) (hr : Confined I (renameTerm q r)),
      buildTerm I (renameTerm q r) hr=pullAction r (buildTerm I q hq) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ ts args => ∀ (ha : ArgumentsConfined I args) (Δ : List Ty) (r : Renaming Γ Δ)
      (hr : ArgumentsConfined I (renameArguments args r)),
      buildArguments I (renameArguments args r) hr=fun i => pullAction r (buildArguments I args ha i)) with
  | var v =>
    intro hq Δ r hr
    exact variablePull r v
  | lam body ih =>
    intro hq Δ r hr
    exact (congrArg (LambdaSpineActionsProof.lambdaAction (renameTerm body r.lift))
      (ih ⟨hq.1.2.2,hq.2⟩ _ r.lift ⟨hr.1.2.2,hr.2⟩)).trans
      (lambdaPull r body (buildTerm I body ⟨hq.1.2.2,hq.2⟩))
  | ordinary f base ih =>
    intro hq Δ r hr
    exact (congrArg (FunctionalSpineActionsProof.ordinaryAction ⟨f,hr.2.1⟩)
      (ih ⟨hq.1.2,hq.2.2⟩ Δ r ⟨hr.1.2,hr.2.2⟩)).trans
      (ordinaryPull r ⟨f,hq.2.1⟩ (buildArguments I base ⟨hq.1.2,hq.2.2⟩))
  | marked f output base ts extras ihb ihe =>
    intro hq Δ r hr
    exact (congrArg₂ (fun b e => FunctionalSpineActionsProof.markedAction ⟨f,hr.2.1⟩ ⟨output,hr.1.1⟩ b ts
        (argumentTypeList (renameArguments extras r) ⟨hr.1.2.2,hr.2.2.2⟩) e)
      (ihb ⟨hq.1.2.1,hq.2.2.1⟩ Δ r ⟨hr.1.2.1,hr.2.2.1⟩)
      (ihe ⟨hq.1.2.2,hq.2.2.2⟩ Δ r ⟨hr.1.2.2,hr.2.2.2⟩)).trans
      (markedPull r ⟨f,hq.2.1⟩ ⟨output,hq.1.1⟩ (buildArguments I base ⟨hq.1.2.1,hq.2.2.1⟩)
        ts (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩) (buildArguments I extras ⟨hq.1.2.2,hq.2.2.2⟩))
  | nil =>
    funext i
    exact Fin.elim0 i
  | cons q rest ihq ihr =>
    rename_i ha Δ r hr
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ihq ⟨ha.1.1,ha.2.1⟩ Δ r ⟨hr.1.1,hr.2.1⟩
    · exact congrFun (ihr ⟨ha.1.2,ha.2.2⟩ Δ r ⟨hr.1.2,hr.2.2⟩) j

theorem literalErasure : StructuralRenamingTargets.LiteralErasure := by
  intro Symbol inst arity I Γ Δ τ r q
  rfl

theorem interpretationCovariance : StructuralRenamingTargets.InterpretationCovariance := by
  intro Symbol inst arity I Γ Δ τ r q M P ρ
  exact congrArg (fun A : PairedAction I Δ τ => A.evaluate M P ρ)
    (buildRename q.val q.property Δ r (renameSource r q).property)

theorem scannerCovariance : StructuralRenamingTargets.ScannerCovariance := by
  intro Symbol inst arity I Γ Δ τ r q M P ρ mask types υ args h
  exact congrArg (fun A : PairedAction I Δ τ => A.scan M P ρ mask types υ args h)
    (buildRename q.val q.property Δ r (renameSource r q).property)

end LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingProof
