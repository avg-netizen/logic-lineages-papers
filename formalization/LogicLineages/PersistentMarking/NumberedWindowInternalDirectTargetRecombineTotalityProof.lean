module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineTotalityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalDirectTargetRecombineProof (exact_LiteralTargetRecombine)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def app (i : Fin 3) : Program 3 := .composition append ![.projection 0,.projection i]

private theorem tapeTwo (x y : OTerm α) :
    (![x,y] : Fin 2 → OTerm α) = Fin.cons x (Fin.cons y Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem getAppend (xs : Fin 3 → OTerm α) (i : Fin 3) (out : OTerm α)
    (a : Nonempty (Derivation B Γ (programGraph (app i) out xs))) :
    Nonempty (Derivation B Γ (appended (xs 0) (xs i) out)) := by
  simpa only [appended,tapeTwo] using
    binaryRecover append (.projection 0) (.projection i) out (xs 0) (xs i) xs a
      (projectionValue 0 xs) (projectionValue i xs)

private theorem renameObs {β : Type} {Δ : List (Formula β)} (x y : OTerm α)
    (a : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![x,y])))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (programGraph permutation (suc z) ![x.relabel j,y.relabel j])) := by
  simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) x y a j keep

/-- The two internal normalization appends are actually opened from the
selected original total graphs. Only the real old and side append reports
remain as premises. -/
theorem exact_LiteralTargetRecombineTotal
    (t kept projected kl kr pl pr keptJoin projectedJoin oldJoin tl tr q : OTerm α)
    (oldAppend : Nonempty (Derivation B Γ (appended kept projected oldJoin)))
    (old : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![t,oldJoin])))
    (ak : Nonempty (Derivation B Γ (appended kl kr keptJoin)))
    (ap : Nonempty (Derivation B Γ (appended pl pr projectedJoin)))
    (fk : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![kept,keptJoin])))
    (fp : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![projected,projectedJoin])))
    (al : Nonempty (Derivation B Γ (appended kl pl tl)))
    (arr : Nonempty (Derivation B Γ (appended kr pr tr)))
    (aq : Nonempty (Derivation B Γ (appended tl tr q))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![t,q])) := by
  apply programsCases (![app 1,app 2] : Fin 2 → Program 3)
    ![keptJoin,projected,projectedJoin] (programGraph permutation (suc z) ![t,q])
  intro β j Δ outs keep report
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  let xs : Fin 3 → OTerm β := ![keptJoin.relabel j,projected.relabel j,projectedJoin.relabel j]
  have h₁ : Nonempty (Derivation B Δ (programGraph (app 1) (outs 0) xs)) := by
    have a := report (0 : Fin 2)
    change Nonempty (Derivation B Δ (programGraph (app 1) (outs 0)
      (fun i : Fin 3 => ((![keptJoin,projected,projectedJoin] : Fin 3 → OTerm α) i).relabel j))) at a
    simpa only [tripleInputsRename,xs] using a
  have h₂ : Nonempty (Derivation B Δ (programGraph (app 2) (outs 1) xs)) := by
    have a := report (1 : Fin 2)
    change Nonempty (Derivation B Δ (programGraph (app 2) (outs 1)
      (fun i : Fin 3 => ((![keptJoin,projected,projectedJoin] : Fin 3 → OTerm α) i).relabel j))) at a
    simpa only [tripleInputsRename,xs] using a
  exact exact_LiteralTargetRecombine (t.relabel j) (kept.relabel j) (projected.relabel j)
    (kl.relabel j) (kr.relabel j) (pl.relabel j) (pr.relabel j) (keptJoin.relabel j)
    (projectedJoin.relabel j) (oldJoin.relabel j) (outs 0) (outs 1)
    (tl.relabel j) (tr.relabel j) (q.relabel j)
    (renamePair append oldJoin kept projected oldAppend j keep) (renameObs t oldJoin old j keep)
    (renamePair append keptJoin kl kr ak j keep) (renamePair append projectedJoin pl pr ap j keep)
    (renameObs kept keptJoin fk j keep) (renameObs projected projectedJoin fp j keep)
    (getAppend xs 1 (outs 0) h₁) (getAppend xs 2 (outs 1) h₂)
    (renamePair append tl kl pl al j keep) (renamePair append tr kr pr arr j keep)
    (renamePair append q tl tr aq j keep)

#print axioms exact_LiteralTargetRecombineTotal
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineTotalityProof
