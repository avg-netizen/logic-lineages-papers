module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GuardedSource GuardedSourceGraphSupportProof GuardedSourceSyntaxProof GuardedSourceCertificateProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem relationClosure (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (tag : Program 2) (window : Program 1) (context : Nat)
    (hc : evaluate window (List.Vector.ofFn ![context]) = 1) (typ x y : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (literalTyped (computability oldComp tag) context typ x)))
    (hr : Nonempty (Derivation body Gamma
      (literalR (source oldSource oldComp.typed tag window) context x y))) :
    Nonempty (Derivation body Gamma (literalTyped (computability oldComp tag) context typ y)) := by
  rw [literalTypedGraph] at ht ⊢
  rw [literalRGraph] at hr
  obtain ⟨dr⟩ := hr
  let P : Formula (α ⊕ Fin 1) := programGraph
    (guardedPositive oldSource.positive oldComp.typed tag window) (suc z)
    ![numeral context,x.relabel Sum.inl,y.relabel Sum.inl,.var (.inr 0)]
  let Delta := P :: Gamma.map weaken
  have htx := renameInto ht Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [programRename,sucRelabel,zRelabel,tupleThreeRename,numeralRename] at htx
  have d := certificateClosure oldComp.typed oldSource.positive tag window
    (numeral context) (typ.relabel Sum.inl) (x.relabel Sum.inl) (y.relabel Sum.inl)
    (.var (.inr 0)) (windowNumeral window context hc) htx
    (show Nonempty (Derivation body Delta P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hd : Nonempty (Derivation body Delta (weaken
      (programGraph (computability oldComp tag).typed (suc z) ![numeral context,typ,y]))) := by
    simpa only [computability,weaken,programRename,sucRelabel,zRelabel,tupleThreeRename,numeralRename] using d
  obtain ⟨dd⟩ := hd
  exact ⟨Derivation.existentialElimination dr dd⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
