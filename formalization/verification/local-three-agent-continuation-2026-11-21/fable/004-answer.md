Nothing below has been compiled; Astra's queue is the first check. All frozen targets and my earlier files are untouched and used as-is.

The proof is the list induction from turn 3 with the invariant `hitScan E n seen ctx ty k := hitGraph E n seen ctx ty k → scanGraph E seen ctx ty k`. Three things are new relative to that packet:

- **Nil is a real contradiction.** The pass output at nil is zero, so the membership premise becomes `memberGraph 0 k`; `nilRecover` on the actual `scratchMember` gives the constant-zero base with output one, and `sucNeZeroApply` refutes it.
- **Head equality from the non-zero head test.** `equalityOfHit` uses the original trichotomy (`actualOriginalComparison`, `compareView`) with `rejectForwardOrder`/`rejectBackwardOrder` at the same `h,k`.
- **Scan transport on the retained branch.** `candidateTransport` moves `scanGraph … h` to `scanGraph … k` along that equality via `graphInputTransport`. This is the one pattern with no precedent in the sparse family, so it sits in a module where `programGraph` is not locally irreducible.

`NumberedWindowInternalSparseRetainedScanSyntaxProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding varBind liftBind sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Subst)
open NumberedWindowInternalSparseDirectedSeen (scanGraph scanTape)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph hitRename)

attribute [local irreducible] programGraph

/-- The induction invariant at one scratch vertices code: a member of the
actual pass output of this code passed the original scan against the
same fixed seen list, context and type. -/
def hitScan (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  (hitGraph E vertices seen ctx ty k).imp (scanGraph E seen ctx ty k)

private theorem hitSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitGraph E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitGraph E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  unfold hitGraph
  rw [graph5Subst,sucSubst,zSubst]

private theorem scanSubst (E : Program 4) {α β : Type} (seen ctx ty v : OTerm α)
    (ts : α → OTerm β) :
    (scanGraph E seen ctx ty v).subst (fun a => emb (ts a)) =
      scanGraph E (seen.subst ts) (ctx.subst ts) (ty.subst ts) (v.subst ts) := by
  have tape : (fun i => ((![seen,ctx,ty,v] : Fin 4 → OTerm α) i).subst ts) =
      ![seen.subst ts,ctx.subst ts,ty.subst ts,v.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun w =>
      Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) w) y) x) i <;> rfl
  simp only [scanGraph,scanTape,programSubst,tape,sucSubst,zSubst]

theorem hitScanRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (j : α → β) :
    (hitScan E vertices seen ctx ty k).relabel j =
      hitScan E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  change ((hitGraph E vertices seen ctx ty k).relabel j).imp
    ((scanGraph E seen ctx ty k).relabel j) = _
  rw [hitRename,scanRename] <;> rfl

private theorem hitScanSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitScan E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitScan E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  simp only [hitScan,impSubst,hitSubst,scanSubst]

/-- Edge program, seen, context, type and candidate are fixed parameters;
only the original scratch vertices code is generalized. -/
abbrev scanInvariant (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  hitScan E (.var (.inr 0)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) (k.relabel Sum.inl)

theorem scanInvariantCode (E : Program 4) {α : Type} (seen ctx ty k n : OTerm α) :
    atCode (scanInvariant E seen ctx ty k) n = hitScan E n seen ctx ty k := by
  rw [atCode,instantiate,bindEmbedding]
  change (hitScan E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [hitScanSubst]
  simp only [liftBind,varBind]

theorem scanInvariantIndex (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) (i : Fin 3) :
    atIndex (scanInvariant E seen ctx ty k) i =
      hitScan E (.var (.inr i)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
        (ty.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (hitScan E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [hitScanRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
```

`NumberedWindowInternalSparseRetainedScanEqualityProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalQuotientComparisonProof (actualOriginalComparison compareView)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A head equality test that is not zero forces internal equality: the
original trichotomy leaves only the equal case, since each strict order
makes the same actual test return zero. -/
theorem equalityOfHit (x y : OTerm α)
    (hit : Nonempty (Derivation body Γ (missGraph x y).not)) :
    Nonempty (Derivation body Γ (eqn x y)) := by
  obtain ⟨no⟩ := hit
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Γ)
  have hl : Nonempty (Derivation body (ltF x y :: Γ) (eqn x y)) := by
    obtain ⟨hz⟩ := rejectForwardOrder (body := body) (Gamma := ltF x y :: Γ) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have miss : Derivation body (ltF x y :: Γ) (missGraph x y) := hz
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination (addHyp no (ltF x y)) miss)⟩
  have hr : Nonempty (Derivation body (ltF y x :: Γ) (eqn x y)) := by
    obtain ⟨hz⟩ := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Γ) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have miss : Derivation body (ltF y x :: Γ) (missGraph x y) := hz
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination (addHyp no (ltF y x)) miss)⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have he : Derivation body Γ ((eqn x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hrest : Derivation body Γ ((eqn x y ⊔ ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction
      (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
        (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

/-- Transport the original scan along an internal equality of its
candidate. Seen, context and type are the same terms on both sides. -/
theorem candidateTransport (E : Program 4) (seen ctx ty h k : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn h k)))
    (scanned : Nonempty (Derivation body Γ (scanGraph E seen ctx ty h))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  apply graphInputTransport body α 4 Γ _ (suc z)
    (![seen,ctx,ty,h] : Fin 4 → OTerm α) (![seen,ctx,ty,k] : Fin 4 → OTerm α) _ scanned
  intro i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) c) b) a) i
  all_goals rw [onEquality]
  all_goals first
    | exact same
    | exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl _⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
```

`NumberedWindowInternalSparseRetainedScanStepProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanStepProof
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
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparseDirectedFilter (cell passGraph restRow restReport filterStep)
open NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof (reportBinder)
open NumberedWindowInternalSparseDirectedFilterOpenChecks (exact_OpenDirectedFilterCons)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro hitCases)
open NumberedWindowInternalSparseRetainedScanSyntaxProof (hitScan hitScanRename)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit candidateTransport)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual membership recursor at nil is the actual constant zero, so
a successful membership bit at nil is refuted inside the calculus. -/
private theorem emptyMember (k : OTerm α) (psi : Formula α)
    (member : Nonempty (Derivation body Γ (memberGraph z k))) :
    Nonempty (Derivation body Γ psi) := by
  have value := nilRecover memberBase memberStep (suc z) (![k] : Fin 1 → OTerm α) member
  obtain ⟨impossible⟩ := valueUnique (constantZero 1) (suc z) z (![k] : Fin 1 → OTerm α)
    value (zeroConstantValue (![k] : Fin 1 → OTerm α))
  exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

/-- Occurrence in the genuine filtered tail: the inductive hypothesis at
the real tail, with the same seen list and the same candidate. -/
private theorem fromTail (E : Program 4) (tail seen ctx ty k rest : OTerm α)
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph rest k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  obtain ⟨hit⟩ := hitIntro E rest tail seen ctx ty k tailRun member
  obtain ⟨ih⟩ := inherited
  exact ⟨Derivation.implicationElimination ih hit⟩

/-- Retained head: invert membership at the actual output cons. A head
hit is an internal equality, along which the head's own scan transports. -/
private theorem retainedCase (E : Program 4) (tail seen ctx ty k out h rest : OTerm α)
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (scannedHead : Nonempty (Derivation body Γ (scanGraph E seen ctx ty h)))
    (built : Nonempty (Derivation body Γ (cell out h rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  let A := (missGraph h k).not
  let B := memberGraph rest k
  obtain ⟨split⟩ := consInversion out h rest k built member
  obtain ⟨s⟩ := scannedHead
  obtain ⟨ih⟩ := inherited
  obtain ⟨run⟩ := tailRun
  have same := equalityOfHit (body := body) (Γ := A :: Γ) h k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨left⟩ := candidateTransport (body := body) (Γ := A :: Γ) E seen ctx ty h k
    same ⟨addHyp s A⟩
  obtain ⟨right⟩ := fromTail (body := body) (Γ := B :: Γ) E tail seen ctx ty k rest
    ⟨addHyp ih B⟩ ⟨addHyp run B⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- Skipped head: the output is the genuine filtered tail itself. -/
private theorem skippedCase (E : Program 4) (tail seen ctx ty k out rest : OTerm α)
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (same : Nonempty (Derivation body Γ (eqn out rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  have moved : Nonempty (Derivation body Γ (memberGraph rest k)) :=
    headTransport scratchMember (suc z) out rest (![k] : Fin 1 → OTerm α) same member
  exact fromTail E tail seen ctx ty k rest inherited tailRun moved

/-- Both physical alternatives of the checked filter row at one genuine
filtered tail; the retained branch keeps the head's actual scan. -/
private theorem withRow (E : Program 4) (h tail seen ctx ty k out rest : OTerm α)
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (member : Nonempty (Derivation body Γ (memberGraph out k)))
    (row : Nonempty (Derivation body Γ (restRow E out h tail rest seen ctx ty))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  let L : Formula α := scanGraph E seen ctx ty h ⊓ cell out h rest
  let R : Formula α := (scanGraph E seen ctx ty h).not ⊓ eqn out rest
  obtain ⟨row⟩ := row
  obtain ⟨ih⟩ := inherited
  obtain ⟨m⟩ := member
  have run : Derivation body Γ (passGraph E rest tail seen ctx ty) :=
    Derivation.conjunctionLeft row
  have alternatives : Derivation body Γ (L ⊔ R) := Derivation.conjunctionRight row
  have hl : Derivation body (L :: Γ) (scanGraph E seen ctx ty h ⊓ cell out h rest) :=
    Derivation.hypothesis List.mem_cons_self
  have hr : Derivation body (R :: Γ) ((scanGraph E seen ctx ty h).not ⊓ eqn out rest) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨left⟩ := retainedCase (body := body) (Γ := L :: Γ) E tail seen ctx ty k out h rest
    ⟨addHyp ih L⟩ ⟨addHyp run L⟩ ⟨Derivation.conjunctionLeft hl⟩
    ⟨Derivation.conjunctionRight hl⟩ ⟨addHyp m L⟩
  obtain ⟨right⟩ := skippedCase (body := body) (Γ := R :: Γ) E tail seen ctx ty k out rest
    ⟨addHyp ih R⟩ ⟨addHyp run R⟩ ⟨Derivation.conjunctionRight hr⟩ ⟨addHyp m R⟩
  exact ⟨disjunctionElimination alternatives
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- One actual cons with an arbitrary filtered output: the checked open
filter law exposes the genuine filtered tail under its own existential. -/
private theorem consScanned (E : Program 4) (code h tail seen ctx ty k out : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (run : Nonempty (Derivation body Γ (passGraph E out code seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  let up : α → α ⊕ Fin 1 := Sum.inl
  let rest : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P : Formula (α ⊕ Fin 1) := reportBinder E out h tail seen ctx ty
  let Δ : List (Formula (α ⊕ Fin 1)) := P :: Γ.map weaken
  have keep : ∀ p ∈ Γ, p.relabel up ∈ Δ :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have inherited' := renameInto inherited up Δ keep
  rw [hitScanRename] at inherited'
  have member' := renameInto member up Δ keep
  rw [graphRename] at member'
  have row : Nonempty (Derivation body Δ (restRow E (out.relabel up) (h.relabel up)
      (tail.relabel up) rest (seen.relabel up) (ctx.relabel up) (ty.relabel up))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have shape : weaken (scanGraph E seen ctx ty k) =
      scanGraph E (seen.relabel up) (ctx.relabel up) (ty.relabel up) (k.relabel up) :=
    scanRename E seen ctx ty k up
  have closed : Nonempty (Derivation body Δ (weaken (scanGraph E seen ctx ty k))) := by
    rw [shape]
    exact withRow E (h.relabel up) (tail.relabel up) (seen.relabel up) (ctx.relabel up)
      (ty.relabel up) (k.relabel up) (out.relabel up) rest inherited' member' row
  obtain ⟨c⟩ := input
  obtain ⟨r⟩ := run
  obtain ⟨law⟩ := exact_OpenDirectedFilterCons E body α Γ code h tail seen ctx ty out
  have raw : Derivation body Γ (restReport E out h tail seen ctx ty) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction c r)
  have report : Derivation body Γ (existsOne P) := raw
  obtain ⟨closed⟩ := closed
  exact ⟨Derivation.existentialElimination report closed⟩

/-- At nil the actual pass output is the actual constant zero; the hit
is then a successful membership bit at nil, which is impossible. -/
private theorem nilFromHit (E : Program 4) (seen ctx ty k : OTerm α)
    (hit : Nonempty (Derivation body Γ (hitGraph E z seen ctx ty k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  apply hitCases E z seen ctx ty k (scanGraph E seen ctx ty k) hit
  intro β j Δ out _ run member
  rw [zRelabel] at run
  have value := nilRecover (constantZero 3) (filterStep E) out
    (![seen.relabel j,ctx.relabel j,ty.relabel j] : Fin 3 → OTerm β) run
  obtain ⟨same⟩ := valueUnique (constantZero 3) out z
    (![seen.relabel j,ctx.relabel j,ty.relabel j] : Fin 3 → OTerm β) value
    (zeroConstantValue (![seen.relabel j,ctx.relabel j,ty.relabel j] : Fin 3 → OTerm β))
  have moved : Nonempty (Derivation body Δ (memberGraph z (k.relabel j))) :=
    headTransport scratchMember (suc z) out z (![k.relabel j] : Fin 1 → OTerm β)
      ⟨same⟩ member
  exact emptyMember (k.relabel j) _ moved

private theorem consFromHit (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k)))
    (hit : Nonempty (Derivation body Γ (hitGraph E code seen ctx ty k))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  apply hitCases E code seen ctx ty k (scanGraph E seen ctx ty k) hit
  intro β j Δ out keep run member
  rw [scanRename]
  have input' := renameInto input j Δ keep
  rw [consGraphRename] at input'
  have inherited' := renameInto inherited j Δ keep
  rw [hitScanRename] at inherited'
  exact consScanned E (code.relabel j) (h.relabel j) (tail.relabel j) (seen.relabel j)
    (ctx.relabel j) (ty.relabel j) (k.relabel j) out input' inherited' run member

/-- Base of the original list induction, at the literal nil code. -/
theorem atNil (E : Program 4) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (hitScan E z seen ctx ty k)) := by
  let H := hitGraph E z seen ctx ty k
  obtain ⟨d⟩ := nilFromHit (body := body) (Γ := H :: Γ) E seen ctx ty k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Constructor step of the original list induction, at an actual cons
graph, from the invariant at its real tail. -/
theorem atCons (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (hitScan E tail seen ctx ty k))) :
    Nonempty (Derivation body Γ (hitScan E code seen ctx ty k)) := by
  let H := hitGraph E code seen ctx ty k
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨d⟩ := consFromHit (body := body) (Γ := H :: Γ) E code h tail seen ctx ty k
    ⟨addHyp c H⟩ ⟨addHyp ih H⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanStepProof
```

`NumberedWindowInternalSparseRetainedScanInductionProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanInductionProof
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
open NumberedWindowInternalSparseDirectedSeen (scanGraph seenWitness)
open NumberedWindowInternalSparseDirectedSeenOpenChecks (exact_OpenDirectedSeenWitness)
open NumberedWindowInternalSparseRetainedScanTargets
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro)
open NumberedWindowInternalSparseRetainedScanSyntaxProof
  (hitScan scanInvariant scanInvariantCode scanInvariantIndex)
open NumberedWindowInternalSparseRetainedScanStepProof (atNil atCons)

private theorem constructorDerivation (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (scanInvariant E seen ctx ty k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ
    (constructorBody (scanInvariant E seen ctx ty k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := hitScan E t (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (scanInvariant E seen ctx ty k) 2).imp
      (atIndex (scanInvariant E seen ctx ty k) 0))))
  simp only [scanInvariantIndex]
  obtain ⟨out⟩ := atCons (body := body) (Γ := Δ) E n h t (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- Induction on the original scratch vertices code inside the original
calculus. Edge, seen, context, type and candidate are fixed; the filtered
output is selected by actual Program totality. -/
theorem retainedScan : ExactRetainedScan := by
  intro E body α Γ vertices seen ctx ty out k
  have base : Nonempty (Derivation body Γ (atCode (scanInvariant E seen ctx ty k) z)) := by
    rw [scanInvariantCode]
    exact atNil E seen ctx ty k
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := constructorDerivation E body α Γ seen ctx ty k
  have original : Nonempty (Derivation body Γ (premises (scanInvariant E seen ctx ty k))) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have current := actualOriginalListInductionAtCode body α Γ (scanInvariant E seen ctx ty k)
    vertices original
  rw [scanInvariantCode] at current
  obtain ⟨law⟩ := current
  let P := passGraph E out vertices seen ctx ty ⊓ memberGraph out k
  have both : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hit⟩ := hitIntro (body := body) (Γ := P :: Γ) E out vertices seen ctx ty k
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  have applied : Derivation body (P :: Γ) (scanGraph E seen ctx ty k) :=
    Derivation.implicationElimination (addHyp law P) hit
  exact ⟨Derivation.implicationIntroduction applied⟩

/-- The checked open scan witness at the very same seen code, context,
type and retained candidate. -/
theorem retainedPredecessor : ExactRetainedPredecessor := by
  intro E body α Γ vertices seen ctx ty out k
  let P := passGraph E out vertices seen ctx ty ⊓ memberGraph out k
  obtain ⟨law⟩ := retainedScan E body α (P :: Γ) vertices seen ctx ty out k
  obtain ⟨witness⟩ := exact_OpenDirectedSeenWitness E body α (P :: Γ) seen ctx ty k
  have both : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  have scanned : Derivation body (P :: Γ) (scanGraph E seen ctx ty k) :=
    Derivation.implicationElimination law both
  have found : Derivation body (P :: Γ) (seenWitness E seen ctx ty k) :=
    Derivation.implicationElimination witness scanned
  exact ⟨Derivation.implicationIntroduction found⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanInductionProof
```

`NumberedWindowInternalSparseRetainedScanChecks.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
open NumberedWindowInternalSparseRetainedScanTargets
open NumberedWindowInternalSparseRetainedScanInductionProof (retainedScan retainedPredecessor)

theorem exact_RetainedScan : ExactRetainedScan := retainedScan

theorem exact_RetainedPredecessor : ExactRetainedPredecessor := retainedPredecessor

#print axioms exact_RetainedScan
#print axioms exact_RetainedPredecessor
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
```

## Source dependencies used

- **Reused from my turn-3 packet, unchanged:** `hitGraph`, `hitRename`, `missGraph` (SyntaxProof); `hitIntro`, `hitCases` (CompositionProof); `consInversion` (MemberConsProof).
- **Filter row:** `exact_OpenDirectedFilterCons`, `reportBinder`, `Derivation.existentialElimination`.
- **Scan:** `scanRename` (public), `exact_OpenDirectedSeenWitness` for the predecessor at the same `seen/ctx/ty/k`. `scanSubst` and `hitSubst` are re-proved locally because the existing copies are `private`.
- **Equality from the head test:** `InternalQuotientComparisonProof.{actualOriginalComparison, compareView}`, `InternalEqualityTestProof.{rejectForwardOrder, rejectBackwardOrder}`, `weakenClosed`.
- **Scan transport:** `InternalGraphCompositionEqualityProof.graphInputTransport`, `onEquality`, `InternalTagArithmeticSupportProof.refl`.
- **Nil impossibility:** `nilRecover` (on `pass` and on `scratchMember`), `zeroConstantValue`, `valueUnique`, `headTransport`, `sucNeZeroApply`.
- **Induction:** `actualOriginalListInductionAtCode`, `actualFiniteUniversalIntroduction`, `InternalListInduction.{atCode, atIndex, constructorBody, constructors, premises}`.
- **Not used:** numerical calibration, standard-model reasoning, ordered-round ancestry.

## Where a first failure is most likely

- **`candidateTransport`:** the `apply graphInputTransport … _ scanned` unification through `scanGraph` → `programGraph` → `graph`, and the `all_goals` closing of the four coordinate goals.
- **`equalityOfHit`:** the cast `have miss : … (missGraph x y) := hz` from `equalityGraph z x y`.
- **`scanSubst`:** the closing `simp only` with the local `tape` hypothesis.
