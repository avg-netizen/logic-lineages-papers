module
public import LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation StructuralRenaming LambdaSpineActions LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem actionExt {Γ : List Ty} {τ : Ty} (A B : PairedAction I Γ τ) (he : A.evaluate=B.evaluate) (hs : A.scan=B.scan) : A=B := by
  cases A
  cases B
  cases he
  cases hs
  rfl

def pullAction {Γ Δ : List Ty} {τ : Ty} (r : Renaming Γ Δ) (A : PairedAction I Γ τ) : PairedAction I Δ τ where
  evaluate := fun M P ρ => A.evaluate M P (reindex r ρ)
  scan := fun M P ρ mask types υ args h => A.scan M P (reindex r ρ) (pullMask r mask) types υ args h
  evaluateMonotone := by
    intro M N P ρ η hMN hρη
    exact A.evaluateMonotone M N P _ _ hMN (fun {_} v => hρη (r v))
  evaluateNatural := by
    intro M P Q h ρ
    exact A.evaluateNatural M P Q h (reindex r ρ)
  scanMonotone := by
    intro M N P ρ η mask types υ args args' h hMN hρη ha
    exact A.scanMonotone M N P _ _ _ types υ args args' h hMN (fun {_} v => hρη (r v)) ha
  scanNatural := by
    intro M P Q hPQ ρ mask types υ args h
    exact A.scanNatural M P Q hPQ (reindex r ρ) (pullMask r mask) types υ args h
  scanEmpty := by
    intro M P ρ mask args
    exact A.scanEmpty M P (reindex r ρ) (pullMask r mask) args

theorem maskLift {Γ Δ : List Ty} {σ : Ty} (r : Renaming Γ Δ) (mask : Protected Δ) :
    @Eq (Protected (σ::Γ)) (pullMask r.lift (protectExtend mask)) (protectExtend (pullMask r mask)) := by
  funext τ v
  cases v <;> rfl

theorem openingReindex {Γ Δ : List Ty} {P : World I} (r : Renaming Γ Δ) (ρ : Environment I Δ P)
    (σ υ : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P σ υ i) :
    @Eq (Environment I (σ::Γ) ⟨(i,σ)::P.val,h.2.1⟩)
      (reindex r.lift (LambdaObservationMatching.openingEnvironment ρ σ υ i h))
      (LambdaObservationMatching.openingEnvironment (reindex r ρ) σ υ i h) := by
  funext τ v
  cases v <;> rfl

theorem consumePull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Δ P) (mask : Protected Δ)
    (α : Ty) (rest : List Ty) (τ : Ty) (args : Values I (α::rest) P) (h : Ty.arrow σ υ=arrows (α::rest) τ) :
    consume (pullAction r.lift A) M P ρ mask α rest τ args h=
      consume A M P (reindex r ρ) (pullMask r mask) α rest τ args h := by
  simp only [consume,pullAction]
  rw [TypedValueEnvironmentProof.reindexLift Symbol inferInstance arity I Γ Δ σ P r,
    maskLift]

theorem nonemptyPull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Δ P) (mask : Protected Δ)
    (types : List Ty) (τ : Ty) (args : Values I types P) (h : Ty.arrow σ υ=arrows types τ) (hn : types≠[]) :
    consumeNonempty (pullAction r.lift A) M P ρ mask types τ args h hn=
      consumeNonempty A M P (reindex r ρ) (pullMask r mask) types τ args h hn := by
  cases types with
  | nil => exact False.elim (hn rfl)
  | cons α rest => exact consumePull r A M P ρ mask α rest τ args h

theorem matchPull {Γ Δ : List Ty} {σ υ : Ty} (r : Renaming Γ Δ)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Δ P) (strict : Bool)
    (t : Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ)) :
    matchTerm strict (bodyEvaluator (renameTerm body r.lift) (pullAction r.lift A) M) ρ t=
      matchTerm strict (bodyEvaluator body A M) (reindex r ρ) t := by
  cases t <;> try rfl
  case lam targetBody =>
    simp only [matchTerm,openedRead,bodyEvaluator,pullAction]
    congr 1
    apply propext
    constructor <;> rintro ⟨i,h,hw⟩
    · refine ⟨i,h,?_⟩
      simpa only [openingReindex] using hw
    · refine ⟨i,h,?_⟩
      simpa only [openingReindex] using hw

end LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingSupportProof
