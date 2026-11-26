module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue outputTransport valueUnique programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalAcceptance (constantZero branch)
open ID1Completion.InternalListCodec (consCode headCode tailCode)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets (stepGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationTargets

private def retained (i : Fin 6) : Prop := i = 1 ∨ i = 2 ∨ i = 3

/-- A static observation about the actual selected step's expression tree:
subprograms can invoke arbitrary original outer programs, but only with
inputs built from the retained source coordinates. -/
private inductive Reads : Program 6 → Prop
  | projection (i : Fin 6) : retained i → Reads (.projection i)
  | composition {n} (f : Program n) (g : Fin n → Program 6) :
      (∀ i, Reads (g i)) → Reads (.composition f g)

private theorem readsOne (p : Program 1) (q : Program 6) (hq : Reads q) :
    Reads (.composition p (fun _ : Fin 1 => q)) :=
  .composition p (fun _ => q) (fun _ => hq)

private theorem readsTwo (p : Program 2) (q r : Program 6) (hq : Reads q) (hr : Reads r) :
    Reads (.composition p ![q,r]) :=
  .composition p ![q,r] (fun i => Fin.cases hq (Fin.cases hr (fun u => Fin.elim0 u)) i)

private theorem readsBranch (c p q : Program 6) (hc : Reads c) (hp : Reads p) (hq : Reads q) :
    Reads (branch c p q) :=
  .composition _ _ (fun i => Fin.cases hc
    (Fin.cases hp (Fin.cases hq (fun u => Fin.elim0 u))) i)

private theorem stepReads (raw : Program 5) (least : Program 3) : Reads (iterateStep raw least) := by
  have prior : Reads (.projection (1 : Fin 6)) := .projection 1 (Or.inl rfl)
  have ctx : Reads (.projection (2 : Fin 6)) := .projection 2 (Or.inr (Or.inl rfl))
  have ty : Reads (.projection (3 : Fin 6)) := .projection 3 (Or.inr (Or.inr rfl))
  have cursor : Reads scratchCursor := readsOne headCode (.projection 1) prior
  have cur : Reads scratchCurrent := readsOne tailCode (.projection 1) prior
  have atRaw (p : Program 1) : Reads (onCursor p) := readsOne p scratchCursor cursor
  have zero : Reads (constantZero 6) := .composition .zero Fin.elim0 (fun i => Fin.elim0 i)
  have call : Reads (advanceAtCell raw least) :=
    .composition (advance raw least) ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
      (fun i => Fin.cases ctx (Fin.cases ty (Fin.cases cur
        (Fin.cases (atRaw cellHead) (fun u => Fin.elim0 u)))) i)
  exact readsBranch scratchCursor (.projection 1) _ cursor prior
    (readsBranch (onCursor cellGood) dead (updateCell raw least) (atRaw cellGood)
      (readsTwo consCode (constantZero 6) (constantZero 6) zero zero)
      (readsTwo consCode (onCursor cellTail) (advanceAtCell raw least) (atRaw cellTail) call))

private theorem transport {body : Positive (Fin 1)} (p : Program 6) (use : Reads p) :
    ∀ (α : Type) (Γ : List (Formula α)) (out : OTerm α) (xs ys : Fin 6 → OTerm α),
      (∀ i, retained i → xs i = ys i) →
      Nonempty (Derivation body Γ (programGraph p out xs)) →
      Nonempty (Derivation body Γ (programGraph p out ys)) := by
  induction use with
  | projection i hi =>
    intro α Γ out xs ys same old
    obtain ⟨eq⟩ := valueUnique (.projection i) out (xs i) xs old (projectionValue i xs)
    rw [same i hi] at eq
    exact outputTransport (.projection i) (ys i) out ys ⟨symm eq⟩ (projectionValue i ys)
  | composition f g reads ih =>
    intro α Γ out xs ys same old
    apply programCompositionCases f g out xs (programGraph (.composition f g) out ys) old
    intro β j mids Δ _ outer inner
    rw [programRename]
    apply compositionValue f g (out.relabel j) (fun i => (ys i).relabel j) mids outer
    intro i
    exact ih i β Δ (mids i) (fun k => (xs k).relabel j) (fun k => (ys k).relabel j)
      (fun k hr => congrArg (fun v => v.relabel j) (same k hr)) (inner i)

theorem moveUnused {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3)
    (out prior c ty k start cert k' start' cert' : OTerm α)
    (h : Nonempty (Derivation body Γ (stepGraph raw least out k prior c ty start cert))) :
    Nonempty (Derivation body Γ (stepGraph raw least out k' prior c ty start' cert')) := by
  apply transport (iterateStep raw least) (stepReads raw least) α Γ out
    (call6 k prior c ty start cert) (call6 k' prior c ty start' cert') _ h
  intro i hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem coordinates : OpenStepCoordinates := by
  intro body raw least α out prior c ty k start cert k' start' cert'
  let a := stepGraph raw least out k prior c ty start cert
  let b := stepGraph raw least out k' prior c ty start' cert'
  have ha : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body [b] b := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := moveUnused raw least out prior c ty k start cert k' start' cert' ⟨ha⟩
  obtain ⟨backward⟩ := moveUnused raw least out prior c ty k' start' cert' k start cert ⟨hb⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateProof
