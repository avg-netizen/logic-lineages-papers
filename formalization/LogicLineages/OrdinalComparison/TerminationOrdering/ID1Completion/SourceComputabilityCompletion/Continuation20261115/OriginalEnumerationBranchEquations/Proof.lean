module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ForwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem backward (n : Nat) (node param vb f ts hs ls tb p2 p3 out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (hw : Nonempty (Derivation body Delta (Targets.successorOutput n out param vb f ts hs ls tb))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Delta
    (WitnessProof.matrix n out param vb f ts hs ls tb) _ hw
  let j : alpha → alpha ⊕ Fin 4 := Sum.inl
  let ys : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  let Theta := WitnessProof.matrix n out param vb f ts hs ls tb :: Delta.map (fun q => q.relabel j)
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hm : Nonempty (Derivation body Theta (WitnessProof.matrix n out param vb f ts hs ls tb)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,sucRelabel] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel] at hpj
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,sucRelabel] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,sucRelabel] at h3j
  rw [graph2Rename]
  exact BackwardProof.atFields n (node.relabel j) (param.relabel j) (vb.relabel j) (f.relabel j)
    (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j) (p2.relabel j) (p3.relabel j)
    (out.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hnj hpj h2j h3j hm

theorem internalSuccessor : Targets.InternalSuccessor := by
  intro n body alpha Delta node param vb f ts hs ls tb p2 p3 out hn hp h2 h3
  exact ⟨ForwardProof.forward n node param vb f ts hs ls tb p2 p3 out hn hp h2 h3,
    backward n node param vb f ts hs ls tb p2 p3 out hn hp h2 h3⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Proof
