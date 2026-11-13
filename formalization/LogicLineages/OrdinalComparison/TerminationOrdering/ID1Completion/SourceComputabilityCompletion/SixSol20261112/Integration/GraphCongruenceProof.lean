module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.GraphCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalRecursionGraph InternalRecursionGraphSyntaxProof
open InternalRecursionGraphZeroEliminationProof InternalRecursionGraphSuccessorEliminationProof
open InternalClosedProgramsBindingProof InternalFiniteBlocksProof
open InternalGraphCompositionSyntaxProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open OriginalTransparentLambdaFinalLogicProof (iffSelf iffReverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem equivalentRefl {n : Nat} (p : Program n) : ProgramGraphEquivalent p p := by
  intro body alpha Delta out xs
  exact iffSelf _

theorem equivalentReverse {n : Nat} {p q : Program n}
    (h : ProgramGraphEquivalent p q) : ProgramGraphEquivalent q p := by
  intro body alpha Delta out xs
  exact iffReverse (h body alpha Delta out xs)

theorem compositionForward {m n : Nat} (p q : Program n)
    (gs hs : Fin n → Program m) (hp : ProgramGraphEquivalent p q)
    (hg : ∀ i, ProgramGraphEquivalent (gs i) (hs i))
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out : OTerm alpha) (xs : Fin m → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (.composition p gs) out xs))) :
    Nonempty (Derivation body Delta (programGraph (.composition q hs) out xs)) := by
  apply programCompositionCases p gs out xs _ h
  intro beta j ys Theta incl houter hinner
  simp only [programRename]
  exact compositionValue q hs (out.relabel j) (fun i => (xs i).relabel j) ys
    (iffForward (hp body beta Theta (out.relabel j) ys) houter)
    (fun i => iffForward (hg i body beta Theta (ys i) (fun a => (xs a).relabel j)) (hinner i))

theorem compositionCongruence {m n : Nat} {p q : Program n}
    {gs hs : Fin n → Program m} (hp : ProgramGraphEquivalent p q)
    (hg : ∀ i, ProgramGraphEquivalent (gs i) (hs i)) :
    ProgramGraphEquivalent (.composition p gs) (.composition q hs) := by
  intro body alpha Delta out xs
  let A := programGraph (.composition p gs) out xs
  let B := programGraph (.composition q hs) out xs
  obtain ⟨hf⟩ := compositionForward p q gs hs hp hg body alpha (A :: Delta) out xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := compositionForward q p hs gs (equivalentReverse hp)
    (fun i => equivalentReverse (hg i)) body alpha (B :: Delta) out xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

/-- Preserve the SAME original beta sequence and change only its initial
graph test. No new recursion run or semantic truth premise is supplied. -/
theorem initialForward {n : Nat} (p q : Program n)
    (hp : ProgramGraphEquivalent p q) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (a b : OTerm alpha) (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (initial (OrdinaryArithmetic.graphFormula p) a b xs))) :
    Nonempty (Derivation body Delta
      (initial (OrdinaryArithmetic.graphFormula q) a b xs)) := by
  unfold initial OrdinaryArithmetic.initialGraph
  rw [actualOriginalUniversalEmbedding]
  apply actualFiniteUniversalIntroduction body alpha 1 Delta
  let v : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := a.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
  let B := b.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
  let P := beta A B z v
  let Theta := P :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  have hh := renameInto h Sum.inl Theta (fun f hf =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [initialRename] at hh
  have hbase := initialElimination Theta (OrdinaryArithmetic.graphFormula p) A B v
    (fun i => (xs i).relabel Sum.inl) hh
    (show Nonempty (Derivation body Theta P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨result⟩ := iffForward
    (hp body (alpha ⊕ Fin 1) Theta v (fun i => (xs i).relabel Sum.inl)) hbase
  exact ⟨Derivation.implicationIntroduction result⟩

/-- Every original guarded step is transported at the same counter,
previous result, next result and parameters of the SAME beta sequence. -/
theorem stepForward {n : Nat} (p q : Program (n + 2))
    (hp : ProgramGraphEquivalent p q) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (a b t : OTerm alpha) (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (step (OrdinaryArithmetic.graphFormula p) a b t xs))) :
    Nonempty (Derivation body Delta
      (step (OrdinaryArithmetic.graphFormula q) a b t xs)) := by
  rw [stepAsBlock]
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let j : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let v : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let w : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := a.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let B := b.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let T := t.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let P := (InternalOriginalOrderSyntaxProof.ltF j T ⊓ beta A B j v) ⊓ beta A B (suc j) w
  let Theta := P :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have hh := renameInto h Sum.inl Theta (fun f hf =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [stepRename] at hh
  have hstep := stepElimination Theta (OrdinaryArithmetic.graphFormula p) A B T j v w
    (fun i => (xs i).relabel Sum.inl) hh
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨result⟩ := iffForward
    (hp body (alpha ⊕ Fin 3) Theta w
      (Fin.cons j (Fin.cons v (fun i => (xs i).relabel Sum.inl)))) hstep
  exact ⟨Derivation.implicationIntroduction result⟩

/-- The actual compiled recursion witnesses are reused verbatim. This
transport does not replace native equality by an internal proof. -/
theorem recursionForward {n : Nat} (p q : Program n) (g h : Program (n + 2))
    (hp : ProgramGraphEquivalent p q) (hg : ProgramGraphEquivalent g h)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out t : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hr : Nonempty (Derivation body Delta
      (programGraph (.recursion p g) out (Fin.cons t xs)))) :
    Nonempty (Derivation body Delta
      (programGraph (.recursion q h) out (Fin.cons t xs))) := by
  change Nonempty (Derivation body Delta
    (recursion (OrdinaryArithmetic.graphFormula p) (OrdinaryArithmetic.graphFormula g) out t xs)) at hr
  apply recursionCases Delta (OrdinaryArithmetic.graphFormula p) (OrdinaryArithmetic.graphFormula g)
    out t xs _ hr
  intro beta j a b Theta incl hi hs hb
  simp only [programRename,InternalRecursionGraphStepSyntaxProof.consTermRename]
  exact recursionIntroduction Theta (OrdinaryArithmetic.graphFormula q) (OrdinaryArithmetic.graphFormula h)
    a b (out.relabel j) (t.relabel j) (fun i => (xs i).relabel j)
    (initialForward p q hp body beta Theta a b (fun i => (xs i).relabel j) hi)
    (stepForward g h hg body beta Theta a b (t.relabel j) (fun i => (xs i).relabel j) hs) hb

theorem recursionCongruence {n : Nat} {p q : Program n} {g h : Program (n + 2)}
    (hp : ProgramGraphEquivalent p q) (hg : ProgramGraphEquivalent g h) :
    ProgramGraphEquivalent (.recursion p g) (.recursion q h) := by
  intro body alpha Delta out xs
  have hx : Fin.cons (xs 0) (fun i => xs i.succ) = xs := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← hx]
  let A := programGraph (.recursion p g) out (Fin.cons (xs 0) (fun i => xs i.succ))
  let B := programGraph (.recursion q h) out (Fin.cons (xs 0) (fun i => xs i.succ))
  obtain ⟨hf⟩ := recursionForward p q g h hp hg body alpha (A :: Delta) out (xs 0)
    (fun i => xs i.succ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := recursionForward q p h g (equivalentReverse hp) (equivalentReverse hg)
    body alpha (B :: Delta) out (xs 0) (fun i => xs i.succ)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.GraphCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.GraphCongruenceProof
