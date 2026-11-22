Nothing below has been compiled; Astra's queue is the first check. The frozen target and all committed Definitions/Targets are untouched.

Three proof decisions the reviewer should see up front:

- **Invariant generalises the output by program totality.** It is quantifier-free: `included E n seen ctx ty k := hitGraph … → memberGraph n k`, where `hitGraph` is the graph of the composition `scratchMember ∘ (pass E, candidate)` on the tape `[n,seen,ctx,ty,k]`. This needs two proof-local programs, `passed` and `memberOfPass`, defined in the new SyntaxProof module. Actual composition introduction and recovery convert between `hitGraph` and `passGraph ⊓ memberGraph out`.
- **Member-on-cons inversion is new** (`consInversion`). It goes through actual `consForward`/`stepCases` and `zeroBranchElim` on `memberStep`. The disjunct is "head test not zero, or member of tail"; the head disjunct transfers to the original cons because `headMatches` never reads the tail-bit slot. No equality-test theory is used.
- **Nil case is pure transport.** `nilRecover` gives `out = 0`, so `memberGraph out k` becomes `memberGraph 0 k`; no nil-impossibility argument is needed.

`NumberedWindowInternalSparseFilterInclusionSyntaxProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding varBind liftBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename graph5Subst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedFilter (pass)

attribute [local irreducible] programGraph

/-- The unchanged physical pass read on [vertices,seen,ctx,ty,candidate].
The candidate slot is ignored; nothing is recomputed. -/
def passed (E : Program 4) : Program 5 :=
  .composition (pass E) ![.projection 0,.projection 1,.projection 2,.projection 3]

/-- The actual scratch membership bit of the actual pass output at the
candidate in slot 4. Program totality selects the one filtered output. -/
def memberOfPass (E : Program 4) : Program 5 :=
  .composition scratchMember ![passed E,.projection 4]

def hitGraph (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  programGraph (memberOfPass E) (suc z) ![vertices,seen,ctx,ty,k]

/-- The induction invariant at one scratch code: occurrence in the pass
output of this code gives occurrence in this same code. -/
def included (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  (hitGraph E vertices seen ctx ty k).imp (memberGraph vertices k)

/-- The actual head equality test of the membership row returns zero. -/
def missGraph {α : Type} (h k : OTerm α) : Formula α :=
  programGraph equalityTest z ![h,k]

theorem hitRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α) (j : α → β) :
    (hitGraph E vertices seen ctx ty k).relabel j =
      hitGraph E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  unfold hitGraph
  rw [graph5Rename,sucRelabel,zRelabel]

private theorem hitSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitGraph E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitGraph E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  unfold hitGraph
  rw [graph5Subst,sucSubst,zSubst]

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem includedRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (j : α → β) :
    (included E vertices seen ctx ty k).relabel j =
      included E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  change ((hitGraph E vertices seen ctx ty k).relabel j).imp
    ((memberGraph vertices k).relabel j) = _
  rw [hitRename,graphRename] <;> rfl

private theorem includedSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (included E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      included E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  simp only [included,impSubst,hitSubst,memberSubst]

theorem missRename {α β : Type} (h k : OTerm α) (j : α → β) :
    (missGraph h k).relabel j = missGraph (h.relabel j) (k.relabel j) := by
  unfold missGraph
  rw [programRename,binaryInputsRename,zRelabel]

theorem missNotRename {α β : Type} (h k : OTerm α) (j : α → β) :
    (missGraph h k).not.relabel j = (missGraph (h.relabel j) (k.relabel j)).not := by
  change ((missGraph h k).relabel j).not = _
  rw [missRename]

theorem splitRename {α β : Type} (h tail k : OTerm α) (j : α → β) :
    ((missGraph h k).not ⊔ memberGraph tail k).relabel j =
      (missGraph (h.relabel j) (k.relabel j)).not ⊔
        memberGraph (tail.relabel j) (k.relabel j) := by
  change ((missGraph h k).relabel j).not ⊔ (memberGraph tail k).relabel j = _
  rw [missRename,graphRename]

/-- Edge program, seen, context, type and candidate are fixed parameters;
only the original scratch vertices code is generalized. -/
abbrev invariant (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) : Formula (α ⊕ Fin 1) :=
  included E (.var (.inr 0)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) (k.relabel Sum.inl)

theorem invariantCode (E : Program 4) {α : Type} (seen ctx ty k n : OTerm α) :
    atCode (invariant E seen ctx ty k) n = included E n seen ctx ty k := by
  rw [atCode,instantiate,bindEmbedding]
  change (included E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [includedSubst]
  simp only [liftBind,varBind]

theorem invariantIndex (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) (i : Fin 3) :
    atIndex (invariant E seen ctx ty k) i =
      included E (.var (.inr i)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
        (ty.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (included E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [includedRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
```

`NumberedWindowInternalSparseFilterInclusionMemberConsProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases consValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique outputTransport)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (oneRename graph3Rename)
open NumberedWindowInternalSparseScratchMembership
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (missGraph missRename missNotRename splitRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A zero head test selects the literal tail-bit branch of the actual
step. The successful step output therefore is the genuine tail bit. -/
private theorem missTail (h tail k previous : OTerm α)
    (miss : Nonempty (Derivation body Γ (missGraph h k)))
    (tailRun : Nonempty (Derivation body Γ (programGraph scratchMember previous ![tail,k])))
    (rowRun : Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k]))) :
    Nonempty (Derivation body Γ (memberGraph tail k)) := by
  let xs : Fin 3 → OTerm α := ![h,previous,k]
  have rejected : Nonempty (Derivation body Γ (programGraph headMatches z xs)) := by
    apply compositionValue equalityTest (![.projection 0,.projection 2] : Fin 2 → Program 3)
      z xs ![h,k] miss
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (fun noIndex => Fin.elim0 noIndex)) i
  have kept := zeroBranchElim headMatches (.projection 1) (constantOne 3) (suc z) xs
    rejected rowRun
  obtain ⟨same⟩ := valueUnique (.projection (1 : Fin 3)) (suc z) previous xs kept
    (projectionValue 1 xs)
  exact outputTransport scratchMember previous (suc z) (![tail,k] : Fin 2 → OTerm α)
    ⟨symm same⟩ tailRun

/-- Classical split on the actual head test at one genuine tail bit. -/
private theorem rowSplit (h tail k previous : OTerm α)
    (tailRun : Nonempty (Derivation body Γ (programGraph scratchMember previous ![tail,k])))
    (rowRun : Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k]))) :
    Nonempty (Derivation body Γ ((missGraph h k).not ⊔ memberGraph tail k)) := by
  let M := missGraph h k
  obtain ⟨tailRun⟩ := tailRun
  obtain ⟨rowRun⟩ := rowRun
  obtain ⟨inTail⟩ := missTail (body := body) (Γ := M :: Γ) h tail k previous
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp tailRun M⟩ ⟨addHyp rowRun M⟩
  have yes : Derivation body Γ (M.imp (M.not ⊔ memberGraph tail k)) :=
    Derivation.implicationIntroduction (orRight inTail)
  have no : Derivation body Γ (M.not.imp (M.not ⊔ memberGraph tail k)) :=
    Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self))
  exact ⟨disjunctionElimination (excludedMiddle M) yes no⟩

/-- Inversion of successful membership at an actual cons: the real head
test is not zero, or the same candidate occurs in the real tail. -/
theorem consInversion (code h tail k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (member : Nonempty (Derivation body Γ (memberGraph code k))) :
    Nonempty (Derivation body Γ ((missGraph h k).not ⊔ memberGraph tail k)) := by
  have step := consForward memberBase memberStep code h tail (suc z)
    (![k] : Fin 1 → OTerm α) input member
  apply stepCases memberBase memberStep (suc z) h tail (![k] : Fin 1 → OTerm α)
    ((missGraph h k).not ⊔ memberGraph tail k) step
  intro β j Δ previous _ tailRun rowRun
  rw [oneRename] at tailRun rowRun
  rw [sucRelabel,zRelabel] at rowRun
  rw [splitRename]
  exact rowSplit (h.relabel j) (tail.relabel j) (k.relabel j) previous tailRun rowRun

/-- A head test that is not zero makes the actual step return one for
every tail bit; the head comparison never reads that slot. -/
private theorem stepHead (h previous k : OTerm α)
    (hit : Nonempty (Derivation body Γ (missGraph h k).not)) :
    Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k])) := by
  apply optionGraphCases headMatches (![h,previous,k] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    simp only [tripleInputsRename] at zero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,previous.relabel j,k.relabel j]
    have miss : Nonempty (Derivation body Δ (missGraph (h.relabel j) (k.relabel j))) := by
      apply compositionRecover equalityTest
        (![.projection 0,.projection 2] : Fin 2 → Program 3)
        z xs (![h.relabel j,k.relabel j] : Fin 2 → OTerm β) zero
      intro i
      exact Fin.cases (projectionValue 0 xs)
        (Fin.cases (projectionValue 2 xs) (fun noIndex => Fin.elim0 noIndex)) i
    have no := renameInto hit j Δ keep
    rw [missNotRename] at no
    obtain ⟨miss⟩ := miss
    obtain ⟨no⟩ := no
    exact ⟨Derivation.explosion (Derivation.implicationElimination no miss)⟩
  · intro β j Δ prior _ nonzero
    simp only [tripleInputsRename] at nonzero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,previous.relabel j,k.relabel j]
    exact successorBranchIntro headMatches (.projection 1) (constantOne 3) (suc z) prior xs
      nonzero (oneConstantValue xs)

/-- The same head on any actual cons, with its own genuine recursive
tail value obtained by original Program totality. -/
theorem headHit (code h tail k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (hit : Nonempty (Derivation body Γ (missGraph h k).not)) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  apply programCases scratchMember ![tail,k] (memberGraph code k)
  intro β j Δ previous keep observed
  rw [graphRename]
  rw [binaryInputsRename] at observed
  have hasCell := renameInto input j Δ keep
  rw [consGraphRename] at hasCell
  have no := renameInto hit j Δ keep
  rw [missNotRename] at no
  let h' := h.relabel j
  let t' := tail.relabel j
  let k' := k.relabel j
  exact consValue memberBase memberStep (code.relabel j) h' t' previous (suc z) ![k']
    hasCell observed (stepHead h' previous k' no)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
```

`NumberedWindowInternalSparseFilterInclusionCompositionProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (pass passGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (passed memberOfPass hitGraph hitRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem passedValue (E : Program 4) (out vertices seen ctx ty k : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out vertices seen ctx ty))) :
    Nonempty (Derivation body Γ (programGraph (passed E) out
      (![vertices,seen,ctx,ty,k] : Fin 5 → OTerm α))) := by
  let xs : Fin 5 → OTerm α := ![vertices,seen,ctx,ty,k]
  apply compositionValue (pass E)
    (![.projection 0,.projection 1,.projection 2,.projection 3] : Fin 4 → Program 5)
    out xs (![vertices,seen,ctx,ty] : Fin 4 → OTerm α) run
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (fun noIndex => Fin.elim0 noIndex)))) i

/-- The actual pass output and its actual membership bit compose to the
literal composed program on the same physical tape. -/
theorem hitIntro (E : Program 4) (out vertices seen ctx ty k : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out vertices seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (hitGraph E vertices seen ctx ty k)) := by
  let xs : Fin 5 → OTerm α := ![vertices,seen,ctx,ty,k]
  have inner := passedValue E out vertices seen ctx ty k run
  apply compositionValue scratchMember (![passed E,.projection 4] : Fin 2 → Program 5)
    (suc z) xs (![out,k] : Fin 2 → OTerm α) member
  intro i
  exact Fin.cases inner
    (Fin.cases (projectionValue 4 xs) (fun noIndex => Fin.elim0 noIndex)) i

/-- Original Program totality selects the filtered output as an object
eigenvariable; the composed graph then gives its actual membership bit. -/
theorem hitCases (E : Program 4) (vertices seen ctx ty k : OTerm α) (psi : Formula α)
    (hit : Nonempty (Derivation body Γ (hitGraph E vertices seen ctx ty k)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (passGraph E out (vertices.relabel j) (seen.relabel j)
        (ctx.relabel j) (ty.relabel j))) →
      Nonempty (Derivation body Δ (memberGraph out (k.relabel j))) →
      Nonempty (Derivation body Δ (psi.relabel j))) :
    Nonempty (Derivation body Γ psi) := by
  apply programCases (pass E) (![vertices,seen,ctx,ty] : Fin 4 → OTerm α) psi
  intro β j Δ out keep run
  rw [quadInputsRename] at run
  have moved := renameInto hit j Δ keep
  rw [hitRename] at moved
  let xs : Fin 5 → OTerm β :=
    ![vertices.relabel j,seen.relabel j,ctx.relabel j,ty.relabel j,k.relabel j]
  have inner := passedValue E out (vertices.relabel j) (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j) run
  have member : Nonempty (Derivation body Δ (memberGraph out (k.relabel j))) := by
    apply compositionRecover scratchMember (![passed E,.projection 4] : Fin 2 → Program 5)
      (suc z) xs (![out,k.relabel j] : Fin 2 → OTerm β) moved
    intro i
    exact Fin.cases inner
      (Fin.cases (projectionValue 4 xs) (fun noIndex => Fin.elim0 noIndex)) i
  exact next β j Δ out keep run member

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
```

`NumberedWindowInternalSparseFilterInclusionStepProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (tailMember)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedFilter (cell passGraph restRow restReport filterStep)
open NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof (reportBinder)
open NumberedWindowInternalSparseDirectedFilterOpenChecks (exact_OpenDirectedFilterCons)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (hitGraph included includedRename missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion headHit)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro hitCases)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Occurrence in the genuine filtered tail: the inductive hypothesis at
the real tail, then the checked tail membership introduction. -/
private theorem fromTail (E : Program 4) (code h tail seen ctx ty k rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph rest k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  obtain ⟨hit⟩ := hitIntro E rest tail seen ctx ty k tailRun member
  obtain ⟨ih⟩ := inherited
  exact tailMember code h tail k input ⟨Derivation.implicationElimination ih hit⟩

/-- Retained head: the output is the literal cons of the same head onto
the genuine filtered tail. Invert membership at that actual output cons. -/
private theorem retained (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (built : Nonempty (Derivation body Γ (cell out h rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let A := (missGraph h k).not
  let B := memberGraph rest k
  obtain ⟨split⟩ := consInversion out h rest k built member
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨run⟩ := tailRun
  obtain ⟨left⟩ := headHit (body := body) (Γ := A :: Γ) code h tail k
    ⟨addHyp c A⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨right⟩ := fromTail (body := body) (Γ := B :: Γ) E code h tail seen ctx ty k rest
    ⟨addHyp c B⟩ ⟨addHyp ih B⟩ ⟨addHyp run B⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- Skipped head: the output is the genuine filtered tail itself. -/
private theorem skipped (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (same : Nonempty (Derivation body Γ (eqn out rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  have moved : Nonempty (Derivation body Γ (memberGraph rest k)) :=
    headTransport scratchMember (suc z) out rest (![k] : Fin 1 → OTerm α) same member
  exact fromTail E code h tail seen ctx ty k rest input inherited tailRun moved

/-- Both physical alternatives of the checked filter row share one
genuine result of the same pass on the real tail. -/
private theorem withRow (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (member : Nonempty (Derivation body Γ (memberGraph out k)))
    (row : Nonempty (Derivation body Γ (restRow E out h tail rest seen ctx ty))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let L : Formula α := scanGraph E seen ctx ty h ⊓ cell out h rest
  let R : Formula α := (scanGraph E seen ctx ty h).not ⊓ eqn out rest
  obtain ⟨row⟩ := row
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨m⟩ := member
  have run : Derivation body Γ (passGraph E rest tail seen ctx ty) :=
    Derivation.conjunctionLeft row
  have alternatives : Derivation body Γ (L ⊔ R) := Derivation.conjunctionRight row
  have hl : Derivation body (L :: Γ) (scanGraph E seen ctx ty h ⊓ cell out h rest) :=
    Derivation.hypothesis List.mem_cons_self
  have hr : Derivation body (R :: Γ) ((scanGraph E seen ctx ty h).not ⊓ eqn out rest) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨left⟩ := retained (body := body) (Γ := L :: Γ) E code h tail seen ctx ty k out rest
    ⟨addHyp c L⟩ ⟨addHyp ih L⟩ ⟨addHyp run L⟩ ⟨Derivation.conjunctionRight hl⟩ ⟨addHyp m L⟩
  obtain ⟨right⟩ := skipped (body := body) (Γ := R :: Γ) E code h tail seen ctx ty k out rest
    ⟨addHyp c R⟩ ⟨addHyp ih R⟩ ⟨addHyp run R⟩ ⟨Derivation.conjunctionRight hr⟩ ⟨addHyp m R⟩
  exact ⟨disjunctionElimination alternatives
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- One actual cons with an arbitrary filtered output: the checked open
filter law exposes the genuine filtered tail under its own existential. -/
private theorem consInclusion (E : Program 4) (code h tail seen ctx ty k out : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (run : Nonempty (Derivation body Γ (passGraph E out code seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let up : α → α ⊕ Fin 1 := Sum.inl
  let rest : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P : Formula (α ⊕ Fin 1) := reportBinder E out h tail seen ctx ty
  let Δ : List (Formula (α ⊕ Fin 1)) := P :: Γ.map weaken
  have keep : ∀ p ∈ Γ, p.relabel up ∈ Δ :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have input' := renameInto input up Δ keep
  rw [consGraphRename] at input'
  have inherited' := renameInto inherited up Δ keep
  rw [includedRename] at inherited'
  have member' := renameInto member up Δ keep
  rw [graphRename] at member'
  have row : Nonempty (Derivation body Δ (restRow E (out.relabel up) (h.relabel up)
      (tail.relabel up) rest (seen.relabel up) (ctx.relabel up) (ty.relabel up))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have shape : weaken (memberGraph code k) =
      memberGraph (code.relabel up) (k.relabel up) := graphRename code k up
  have closed : Nonempty (Derivation body Δ (weaken (memberGraph code k))) := by
    rw [shape]
    exact withRow E (code.relabel up) (h.relabel up) (tail.relabel up) (seen.relabel up)
      (ctx.relabel up) (ty.relabel up) (k.relabel up) (out.relabel up) rest
      input' inherited' member' row
  obtain ⟨c⟩ := input
  obtain ⟨r⟩ := run
  obtain ⟨law⟩ := exact_OpenDirectedFilterCons E body α Γ code h tail seen ctx ty out
  have raw : Derivation body Γ (restReport E out h tail seen ctx ty) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction c r)
  have report : Derivation body Γ (existsOne P) := raw
  obtain ⟨closed⟩ := closed
  exact ⟨Derivation.existentialElimination report closed⟩

/-- At nil the actual pass output is the actual constant zero, so the
membership premise transports to the same nil; no bit is inserted. -/
private theorem nilInclusion (E : Program 4) (seen ctx ty k out : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out z seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph z k)) := by
  have value := nilRecover (constantZero 3) (filterStep E) out
    (![seen,ctx,ty] : Fin 3 → OTerm α) run
  obtain ⟨same⟩ := valueUnique (constantZero 3) out z (![seen,ctx,ty] : Fin 3 → OTerm α)
    value (zeroConstantValue (![seen,ctx,ty] : Fin 3 → OTerm α))
  exact headTransport scratchMember (suc z) out z (![k] : Fin 1 → OTerm α) ⟨same⟩ member

private theorem nilFromHit (E : Program 4) (seen ctx ty k : OTerm α)
    (hit : Nonempty (Derivation body Γ (hitGraph E z seen ctx ty k))) :
    Nonempty (Derivation body Γ (memberGraph z k)) := by
  apply hitCases E z seen ctx ty k (memberGraph z k) hit
  intro β j Δ out _ run member
  rw [graphRename,zRelabel]
  rw [zRelabel] at run
  exact nilInclusion E (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j) out
    run member

private theorem consFromHit (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (hit : Nonempty (Derivation body Γ (hitGraph E code seen ctx ty k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  apply hitCases E code seen ctx ty k (memberGraph code k) hit
  intro β j Δ out keep run member
  rw [graphRename]
  have input' := renameInto input j Δ keep
  rw [consGraphRename] at input'
  have inherited' := renameInto inherited j Δ keep
  rw [includedRename] at inherited'
  exact consInclusion E (code.relabel j) (h.relabel j) (tail.relabel j) (seen.relabel j)
    (ctx.relabel j) (ty.relabel j) (k.relabel j) out input' inherited' run member

/-- Base of the original list induction, at the literal nil code. -/
theorem atNil (E : Program 4) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (included E z seen ctx ty k)) := by
  let H := hitGraph E z seen ctx ty k
  obtain ⟨d⟩ := nilFromHit (body := body) (Γ := H :: Γ) E seen ctx ty k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Constructor step of the original list induction, at an actual cons
graph, from the invariant at its real tail. -/
theorem atCons (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k))) :
    Nonempty (Derivation body Γ (included E code seen ctx ty k)) := by
  let H := hitGraph E code seen ctx ty k
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨d⟩ := consFromHit (body := body) (Γ := H :: Γ) E code h tail seen ctx ty k
    ⟨addHyp c H⟩ ⟨addHyp ih H⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionStepProof
```

`NumberedWindowInternalSparseFilterInclusionInductionProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseFilterInclusionTargets
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (hitGraph included invariant invariantCode invariantIndex)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro)
open NumberedWindowInternalSparseFilterInclusionStepProof (atNil atCons)

private theorem constructorDerivation (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (invariant E seen ctx ty k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ
    (constructorBody (invariant E seen ctx ty k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := included E t (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (invariant E seen ctx ty k) 2).imp
      (atIndex (invariant E seen ctx ty k) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := atCons (body := body) (Γ := Δ) E n h t (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- The induction is on the original scratch vertices code inside the
original arithmetic calculus. Edge, seen, context, type and candidate
are fixed; the filtered output is selected by actual Program totality. -/
theorem inclusion : ExactDirectedPassInclusion := by
  intro E body α Γ out vertices seen ctx ty k
  have base : Nonempty (Derivation body Γ (atCode (invariant E seen ctx ty k) z)) := by
    rw [invariantCode]
    exact atNil E seen ctx ty k
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := constructorDerivation E body α Γ seen ctx ty k
  have original : Nonempty (Derivation body Γ (premises (invariant E seen ctx ty k))) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have current := actualOriginalListInductionAtCode body α Γ (invariant E seen ctx ty k)
    vertices original
  rw [invariantCode] at current
  obtain ⟨law⟩ := current
  let P := passGraph E out vertices seen ctx ty ⊓ memberGraph out k
  have both : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hit⟩ := hitIntro (body := body) (Γ := P :: Γ) E out vertices seen ctx ty k
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  have applied : Derivation body (P :: Γ) (memberGraph vertices k) :=
    Derivation.implicationElimination (addHyp law P) hit
  exact ⟨Derivation.implicationIntroduction applied⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionInductionProof
```

`NumberedWindowInternalSparseFilterInclusionChecks.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
open NumberedWindowInternalSparseFilterInclusionTargets
open NumberedWindowInternalSparseFilterInclusionInductionProof (inclusion)

theorem exact_DirectedPassInclusion : ExactDirectedPassInclusion := inclusion

#print axioms exact_DirectedPassInclusion
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
```

## Source dependencies used

- **Frozen target, unchanged:** `ExactDirectedPassInclusion`, `PassIncluded`.
- **Induction on the original vertices code:**
  - `InternalListInductionProof.actualOriginalListInductionAtCode`
  - `InternalClosedProgramsBindingProof.actualFiniteUniversalIntroduction`
  - `InternalListInduction.{atCode, atIndex, constructorBody, constructors, premises}`

  The shape copies `ScratchMembershipOpenInductionProof` and `ScratchMembershipOpenSyntaxProof`.
- **Retain/skip at the genuine filtered tail:**
  - `DirectedFilterOpenChecks.exact_OpenDirectedFilterCons`
  - `DirectedFilterOpenSyntaxProof.reportBinder`
  - `Derivation.existentialElimination`
- **Raw list recursion:** `InternalRawListRecursionProof.{nilRecover, consForward, stepCases, consValue}`.
- **Membership:** `tailMember` (checked introduction); `consInversion` and `headHit` are new here.
- **Control and composition:**
  - `zeroBranchElim`, `successorBranchIntro`
  - `programCases`, `compositionRecover`, `compositionValue`
  - `projectionValue`, `valueUnique`, `outputTransport`, `headTransport`
  - `zeroConstantValue`, `oneConstantValue`
  - `optionGraphCases`, `renameInto`
- **Logic:** `excludedMiddle`, `disjunctionElimination`, `orLeft`, `orRight`, `addHyp`, `symm`.
- **Syntax:**
  - `programRename`, `programSubst`
  - `graph5Rename`, `graph5Subst`, `graph3Rename`, `oneRename`
  - `binaryInputsRename`, `tripleInputsRename`, `quadInputsRename`
  - `graphRename`, `consGraphRename`, `impSubst`
  - the `InternalTagArithmeticSyntaxProof` relabel/subst lemmas
- **Not used:** numerical calibration, standard-model reasoning, equality-test acceptance lemmas, any change to existing files.

## Where a first failure is most likely

- **`invariantCode` / `invariantIndex`:** the `change` lines and the closing `simp only … <;> rfl`.
- **`consInclusion`:** the let-bound context `Δ` and the `weaken` shape rewrite before `existentialElimination`.
- **`cell` versus `consGraph`:** the definitional casts in `retained`, `withRow` and `consInclusion`.
