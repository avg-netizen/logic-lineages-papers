module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftRelocationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptBinaryChoicesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftFinishProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalOriginKeptBinaryChoicesProof (threeBinaryCases renameBinary)
open NumberedWindowInternalOriginKeptInductionSyntaxProof (splitRename)
open NumberedWindowInternalOriginKeptSplitTargets
open NumberedWindowInternalOriginKeptNilProof (packSplit)
open NumberedWindowInternalOriginKeptLeftRelocationLocalProof (App Cmp)
open NumberedWindowInternalOriginKeptLeftRelocationProof (exact_OriginalKeptSplitRelocateLeft)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem appTwo (l r out : OTerm α) : graph2 append out l r = App l r out := by
  have e : (Fin.cons l (Fin.cons r Fin.elim0) : Fin 2 → OTerm α) = ![l,r] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  simp only [graph2,App,e]

/-- Fixed open tape inputs and the five already held reports; none are
chosen by the subsequent evaluation of the six new graph outputs. -/
structure Held (B : Positive (Fin 1)) (Γ : List (Formula α))
    (l r k d t e h s u : OTerm α) (w : Fin 8 → OTerm α) : Prop where
  old : Nonempty (Derivation B Γ (evidence l r t e w))
  cmp : Nonempty (Derivation B Γ (Cmp (w 1) u))
  kept : Nonempty (Derivation B Γ (consGraph k h t))
  removed : Nonempty (Derivation B Γ (consGraph e h d))
  shorter : Nonempty (Derivation B Γ (consGraph u h s))

theorem renameHeld {β : Type} {Δ : List (Formula β)}
    (l r k d t e h s u : OTerm α) (w : Fin 8 → OTerm α)
    (x : Held B Γ l r k d t e h s u w) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Held B Δ (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) (t.relabel j)
      (e.relabel j) (h.relabel j) (s.relabel j) (u.relabel j) (fun i => (w i).relabel j) := by
  constructor
  · simpa only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel] using
      (renameInto x.old j Δ keep)
  · simpa only [Cmp,programRename,binaryInputsRename,sucRelabel,zRelabel] using (renameInto x.cmp j Δ keep)
  · simpa only [consGraphRename] using (renameInto x.kept j Δ keep)
  · simpa only [consGraphRename] using (renameInto x.removed j Δ keep)
  · simpa only [consGraphRename] using (renameInto x.shorter j Δ keep)

private theorem assemble (l r k d t e h s u lk mid source : OTerm α) (w : Fin 8 → OTerm α)
    (x : Held B Γ l r k d t e h s u w)
    (leftK : Nonempty (Derivation B Γ (consGraph lk h (w 0))))
    (leftMid : Nonempty (Derivation B Γ (graph2 append mid (w 0) u)))
    (leftSrc : Nonempty (Derivation B Γ (graph2 append source lk s))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  apply threeBinaryCases consCode append consCode h (w 6) s (w 3) h false (splitExists l r k d)
  intro β j Δ newKeep newRemove longRemove keep hK hD hL
  have held := renameHeld l r k d t e h s u w x j keep
  let W : Fin 8 → OTerm β := fun i => (w i).relabel j
  have lk' := renameBinary consCode lk h (w 0) leftK j keep
  have m' := renameBinary append mid (w 0) u leftMid j keep
  have a' := renameBinary append source lk s leftSrc j keep
  rw [splitRename]
  rw [appTwo] at m' a' hD
  have ev := exact_OriginalKeptSplitRelocateLeft (l.relabel j) (r.relabel j) (t.relabel j)
    (d.relabel j) (k.relabel j) (e.relabel j) (h.relabel j) (s.relabel j) (u.relabel j)
    (lk.relabel j) (mid.relabel j) (source.relabel j) newKeep newRemove longRemove
    W held.old held.cmp held.kept held.removed held.shorter lk' m' a' hK hD hL
  exact packSplit (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j)
    ![lk.relabel j,s.relabel j,W 2,W 3,source.relabel j,W 5,newKeep,newRemove] ev

/-- Generate every required physical append/cons output and repack the
actual left-origin relocation. The occurrence eraser precedes this step. -/
theorem exact_OriginalKeptLeftFinish (l r k d t e h s u : OTerm α) (w : Fin 8 → OTerm α)
    (x : Held B Γ l r k d t e h s u w) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  apply threeBinaryCases consCode append append h (w 0) (w 0) u s true (splitExists l r k d)
  intro β j Δ lk mid source keep hK hM hS
  rw [splitRename]
  exact assemble (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) (t.relabel j)
    (e.relabel j) (h.relabel j) (s.relabel j) (u.relabel j) lk mid source
    (fun i => (w i).relabel j) (renameHeld l r k d t e h s u w x j keep) hK hM hS

#print axioms renameHeld
#print axioms exact_OriginalKeptLeftFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftFinishProof
