module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowRowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename valueUnique outputTransport compositionValue recursionZeroValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldParser (scratchTable scratchBase scratchRow scratchStep)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem zeroRow (R : Program 4) (ctx : OTerm α) : D B Γ (contextRow R z z ctx) := by
  apply programCases consCode (![z,z] : Fin 2 → OTerm α) _
  intro β j Δ table _ code
  simp only [contextRow,programRename,tripleInputsRename,zRelabel]
  simp only [binaryInputsRename,zRelabel] at code
  let c := ctx.relabel j
  let base := constantZero 2
  have atBase : D B Δ (programGraph (scratchBase base) table ![c,z]) := by
    apply compositionValue consCode ![base,constantZero 2] table ![c,z] ![z,z] code
    intro i
    exact Fin.cases (constantZeroValue ![c,z]) (Fin.cases (constantZeroValue ![c,z]) (fun k => Fin.elim0 k)) i
  have tab := recursionZeroValue (scratchBase base) (scratchStep R) table ![c,z] atBase
  obtain ⟨head⟩ := consDestruction table z z code
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable base R) z ![z,c,z] ![table]
    ⟨Derivation.conjunctionLeft head⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact tab

private theorem withTable (R : Program 4) (ctx prior old ty : OTerm α) (goal : Formula α)
    (held : D B Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty (suc prior)))
    (table : D B Γ (contextTable R old prior ctx))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (contextTable R (old.relabel j) (prior.relabel j) (ctx.relabel j)) →
      D B Δ (contextStep R (suc (ty.relabel j)) (prior.relabel j) (old.relabel j) (ctx.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases R ![prior,old,ctx,z] goal
  intro β j Δ value keep update
  simp only [quadInputsRename,zRelabel] at update
  have parent := renameInto held j Δ keep
  have tab := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] at parent
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at tab
  let f := selectedIntrinsic R
  let c := ctx.relabel j
  let p := prior.relabel j
  let o := old.relabel j
  let t := ty.relabel j
  have selected := (exact_OpenIntrinsicQuery f B β Δ c t (suc p)).mp parent
  have canonical := (sameContext R (suc t) c (suc p)).mp selected
  have got := exact_OpenContextMemoSuccessor R B β Δ value p o c tab update
  have agrees := valueUnique (scratchRow (constantZero 2) R)
    value (suc t) ![suc p,c,z] got canonical
  have aligned := outputTransport R value (suc t) ![p,o,c,z] agrees update
  exact use β j Δ keep tab aligned

/-- A successful query at its actual successor key opens both the
original same-context prefix table and its actual successful last row.
The outputs are not chosen independently of the query. -/
theorem exact_OpenContextWindowRow (R : Program 4) (ctx prior ty : OTerm α) (goal : Formula α)
    (held : D B Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty (suc prior)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (contextTable R old (prior.relabel j) (ctx.relabel j)) →
      D B Δ (contextStep R (suc (ty.relabel j)) (prior.relabel j) old (ctx.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases (scratchTable (constantZero 2) R) ![prior,ctx,z] goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  have parent := renameInto held j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] at parent
  apply withTable R (ctx.relabel j) (prior.relabel j) old (ty.relabel j) (goal.relabel j) parent table
  intro γ k Ω stay finalTable last
  have all (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
    simpa only [formulaRelabelComposition] using stay _ (keep f hf)
  have result := use γ (k ∘ j) Ω (old.relabel k) all
    (by simpa only [Term.relabel_relabel] using finalTable)
    (by simpa only [Term.relabel_relabel] using last)
  simpa only [formulaRelabelComposition] using result

#print axioms zeroRow
#print axioms exact_OpenContextWindowRow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowRowProof
