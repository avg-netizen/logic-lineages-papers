module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextMemoProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveClassesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedDualMemoProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowInternalLiteralTypedContextMemoProof (selectedContextMemo)
open NumberedWindowInternalLiteralTypedRecursiveClassesProof (TypedEdgeRefines)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def orderedMemo (R : Program 4) (a b : Fin 4) : Program 4 :=
  .composition (selectedContextMemo R) (Fin.cons (.projection 0)
    (Fin.cons (.projection a) (Fin.cons (.projection b) Fin.elim0)))

/-- The externally selected checker asks for both orientations of the same
physical contextual memo. The original base still enforces both windows
and the originally requested type, independently of its scratch rows. -/
def dualContextMemo (Base R : Program 4) : Program 4 :=
  conjunction Base (conjunction (orderedMemo R 2 3) (orderedMemo R 3 2))

def memoBit {α : Type} (R : Program 4) (ctx q r : OTerm α) : Formula α :=
  programGraph (selectedContextMemo R) (suc z) ![ctx,q,r]

private theorem orderedReports (R : Program 4) (xs : Fin 4 → OTerm α) (out : OTerm α)
    (a b : Fin 4) : D B Γ (programGraph (orderedMemo R a b) out xs) ↔
      D B Γ (programGraph (selectedContextMemo R) out ![xs 0,xs a,xs b]) := by
  let ps : Fin 3 → Program 4 := Fin.cons (.projection 0)
    (Fin.cons (.projection a) (Fin.cons (.projection b) Fin.elim0))
  have reads : ∀ i, D B Γ (programGraph (ps i) (![xs 0,xs a,xs b] i) xs) := fun i =>
    Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue a xs)
      (Fin.cases (projectionValue b xs) (fun k => Fin.elim0 k))) i
  constructor
  · intro checked
    exact compositionRecover (selectedContextMemo R) ps out xs ![xs 0,xs a,xs b] checked reads
  · intro checked
    exact compositionValue (selectedContextMemo R) ps out xs ![xs 0,xs a,xs b] checked reads

theorem exact_OpenDualContextMemo (Base R : Program 4) (ctx ty q r : OTerm α) :
    D B Γ (acceptEdge (dualContextMemo Base R) ctx ty q r) ↔
      D B Γ (acceptEdge Base ctx ty q r) ∧ D B Γ (memoBit R ctx q r) ∧ D B Γ (memoBit R ctx r q) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,q,r]
  let forward := orderedMemo R 2 3
  let reverse := orderedMemo R 3 2
  constructor
  · intro checked
    obtain ⟨c⟩ := conjunctionRecover Base (conjunction forward reverse) xs checked
    obtain ⟨e⟩ := conjunctionRecover forward reverse xs ⟨Derivation.conjunctionRight c⟩
    exact ⟨⟨Derivation.conjunctionLeft c⟩,
      (orderedReports R xs (suc z) 2 3).mp ⟨Derivation.conjunctionLeft e⟩,
      (orderedReports R xs (suc z) 3 2).mp ⟨Derivation.conjunctionRight e⟩⟩
  · rintro ⟨base,f,r⟩
    exact conjunctionAccept Base (conjunction forward reverse) xs base
      (conjunctionAccept forward reverse xs ((orderedReports R xs (suc z) 2 3).mpr f)
        ((orderedReports R xs (suc z) 3 2).mpr r))

theorem exact_OpenDualContextMemoBase (Base R : Program 4) :
    TypedEdgeRefines (dualContextMemo Base R) Base := by
  intro B α Γ ctx ty q r h
  exact ((exact_OpenDualContextMemo Base R ctx ty q r).mp h).1

theorem exact_OpenDualContextMemoReverse (Base R : Program 4) (reverse : CanReverse Base) :
    CanReverse (dualContextMemo Base R) := by
  intro B α Γ ctx ty q r h
  obtain ⟨base, f, rr⟩ := (exact_OpenDualContextMemo Base R ctx ty q r).mp h
  exact (exact_OpenDualContextMemo Base R ctx ty r q).mpr ⟨reverse B α Γ ctx ty q r base,rr,f⟩

theorem exact_OpenDualContextMemoCover (C : Program 3) (s : Settings) (Base R : Program 4)
    (cover : KeepsCover C s Base) : KeepsCover C s (dualContextMemo Base R) := by
  intro B α Γ ctx ty q r a b h ha hb
  exact cover B α Γ ctx ty q r a b ((exact_OpenDualContextMemo Base R ctx ty q r).mp h).1 ha hb

#print axioms exact_OpenDualContextMemo
#print axioms exact_OpenDualContextMemoBase
#print axioms exact_OpenDualContextMemoReverse
#print axioms exact_OpenDualContextMemoCover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedDualMemoProof
