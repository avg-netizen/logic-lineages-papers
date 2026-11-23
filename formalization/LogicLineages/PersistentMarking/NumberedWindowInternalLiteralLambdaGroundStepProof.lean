module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenElimProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaGroundStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalAccessibilityIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralRefinedAuxEdgeProof (lambdaAppCode)
open NumberedWindowInternalBetaSub (betaChecker)
open NumberedWindowInternalBetaCheckerOpenElimProof (substitution)
open NumberedWindowComputabilityFormulaTargets (formula)

def ReachesInstance {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α))
    (guard argSlot bodySlot sub : Program 2) (least : Program 3)
    (ctx dom cod body arg target : OTerm α) : Prop :=
  let raw := auxiliaryTerm dom cod (lambdaTerm dom body) arg
  ∃ k rawDst selected,
    Nonempty (Derivation B Γ (programGraph guard (suc k) ![raw,rawDst])) ∧
    Nonempty (Derivation B Γ (programGraph argSlot arg ![raw,rawDst])) ∧
    Nonempty (Derivation B Γ (programGraph bodySlot body ![raw,rawDst])) ∧
    Nonempty (Derivation B Γ (programGraph (betaChecker guard argSlot bodySlot sub) (suc z) ![raw,rawDst])) ∧
    Nonempty (Derivation B Γ (programGraph least (suc selected) ![ctx,cod,rawDst])) ∧
    Nonempty (Derivation B Γ (equal target (addressTerm ctx cod selected)))

/-- Actual substitution success, physical least selection and endpoint
identity are passed together to the same-body body-instance hypothesis. -/
def InstanceAccess (S : Data) (n : Nat) (sub : Program 2) (least : Program 3) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (ctx cod body arg rawDst selected target : OTerm α),
    Nonempty (Derivation (sourceBody S n) Γ (programGraph sub (suc rawDst) ![arg,body])) →
    Nonempty (Derivation (sourceBody S n) Γ (programGraph least (suc selected) ![ctx,cod,rawDst])) →
    Nonempty (Derivation (sourceBody S n) Γ (equal target (addressTerm ctx cod selected))) →
    Nonempty (Derivation (sourceBody S n) Γ (membership false target))

/-- Exact open beta-local exit. The physical sub report is recovered,
not taken as a second premise or inferred from numeric calibration. -/
theorem exact_OpenLiteralLambdaBetaExit (S : Data) (n : Nat)
    (guard argSlot bodySlot sub : Program 2) (least : Program 3)
    {α : Type} {Γ : List (Formula α)}
    (ctx dom cod body arg target : OTerm α)
    (route : ReachesInstance (sourceBody S n) Γ guard argSlot bodySlot sub least ctx dom cod body arg target)
    (paid : InstanceAccess S n sub least) :
    Nonempty (Derivation (sourceBody S n) Γ (membership false target)) := by
  obtain ⟨k,rawDst,selected,g,a,b,test,sel,eq⟩ := route
  let raw := auxiliaryTerm dom cod (lambdaTerm dom body) arg
  exact paid α Γ ctx cod body arg rawDst selected target
    (substitution guard argSlot bodySlot sub raw rawDst arg body k g a b test) sel eq

/-- Actual local ground constructor rule for the held literal lambda
application. Coverage of original successors and ground C for nonbeta
exits (such as a genuine lifted body step) are explicit obligations.
The beta branch itself must provide physical original checker reports. -/
theorem exact_OpenLiteralLambdaGroundStep (S : Data) (n : Nat) (p : Program 3)
    (guard argSlot bodySlot sub : Program 2) (least : Program 3)
    {α : Type} {Γ : List (Formula α)} (ctx dom cod body arg : OTerm α)
    (admitted : Nonempty (Derivation (sourceBody S n) Γ
      (carrier S false n (lambdaAppCode ctx dom cod body arg))))
    (paid : InstanceAccess S n sub least)
    (cover : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (target : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation (sourceBody S n) Δ
        (edge S false n ((lambdaAppCode ctx dom cod body arg).relabel j) target)) →
      ReachesInstance (sourceBody S n) Δ guard argSlot bodySlot sub least
        (ctx.relabel j) (dom.relabel j) (cod.relabel j) (body.relabel j) (arg.relabel j) target ∨
      Nonempty (Derivation (sourceBody S n) Δ (membership false target))) :
    Nonempty (Derivation (sourceBody S n) Γ (formula p .ground (lambdaAppCode ctx dom cod body arg))) := by
  let src := lambdaAppCode ctx dom cod body arg
  change Nonempty (Derivation (sourceBody S n) Γ (membership false src))
  apply actualOriginalAccessibilityIntroduction S false n α Γ src admitted
  let β := α ⊕ Fin 1
  let ρ : α → β := Sum.inl
  let target : OTerm β := .var (.inr 0)
  let A := edge S false n (src.relabel ρ) target
  let Δ := A :: Γ.map weaken
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ :=
    fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have happened : Nonempty (Derivation (sourceBody S n) Δ A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have each : Nonempty (Derivation (sourceBody S n) Δ (membership false target)) := by
    rcases cover β ρ Δ target keep happened with hit | other
    · exact exact_OpenLiteralLambdaBetaExit S n guard argSlot bodySlot sub least
        (ctx.relabel ρ) (dom.relabel ρ) (cod.relabel ρ) (body.relabel ρ) (arg.relabel ρ) target hit paid
    · exact other
  obtain ⟨each⟩ := each
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction each)⟩

#print axioms exact_OpenLiteralLambdaBetaExit
#print axioms exact_OpenLiteralLambdaGroundStep
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaGroundStepProof
