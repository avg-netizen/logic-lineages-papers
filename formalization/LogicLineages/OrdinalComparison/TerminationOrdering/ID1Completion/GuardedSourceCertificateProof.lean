module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GuardedSource GuardedSourceGraphSupportProof InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem certificateWithSourceTag (typed : Program 3) (positive : Program 4)
    (tag : Program 2) (window : Program 1) (a c typ x y k : OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph window (suc z) ![c])))
    (hx : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (ht : Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph (guardedPositive positive typed tag window)
      (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,y])) := by
  apply programCases tag ![c,y] _
  intro β j Delta b hj hb
  simp only [programRename,sucRelabel,zRelabel,tupleThreeRename]
  have hw' := renameInto hw j Delta hj
  have hx' := renameInto hx j Delta hj
  have ht' := renameInto ht j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [programRename,sucRelabel,zRelabel,tupleOneRename,tupleTwoRename,
    tupleThreeRename,tupleFourRename] at hw' hx' ht' hp' hb
  exact certificateAtTags typed positive tag window (a.relabel j) b (c.relabel j)
    (typ.relabel j) (x.relabel j) (y.relabel j) (k.relabel j) hw' hx' hb ht' hp'

/-- Both extractor values are supplied by original existential graph rules.
No interpretation of the arbitrary source Programs occurs in this proof. -/
theorem certificateClosure (typed : Program 3) (positive : Program 4)
    (tag : Program 2) (window : Program 1) (c typ x y k : OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph window (suc z) ![c])))
    (ht : Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph (guardedPositive positive typed tag window)
      (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,y])) := by
  apply programCases tag ![c,x] _
  intro β j Delta a hj ha
  simp only [programRename,sucRelabel,zRelabel,tupleThreeRename]
  have hw' := renameInto hw j Delta hj
  have ht' := renameInto ht j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [programRename,sucRelabel,zRelabel,tupleOneRename,tupleTwoRename,
    tupleThreeRename,tupleFourRename] at hw' ht' hp' ha
  exact certificateWithSourceTag typed positive tag window a (c.relabel j)
    (typ.relabel j) (x.relabel j) (y.relabel j) (k.relabel j) hw' ha ht' hp'

/-- The only semantic input is one fully concrete natural evaluation; the
resulting original Derivation is built by the numeral-evaluation theorem. -/
theorem windowNumeral (window : Program 1) (context : Nat)
    (hc : evaluate window (List.Vector.ofFn ![context]) = 1) :
    Nonempty (Derivation body Gamma (programGraph window (suc z) ![numeral context])) := by
  have hv : (fun i => (numeral ((List.Vector.ofFn ![context]).get i) : OTerm α)) =
      ![numeral context] := by
    funext i
    exact Fin.cases rfl (fun q => Fin.elim0 q) i
  obtain ⟨d⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 1 window (List.Vector.ofFn ![context]) α
  rw [hc,hv] at d
  exact ⟨weakenClosed d Gamma⟩

theorem actualOriginalGuardedCertificatePreservation :
    GuardedSourceTargets.ActualOriginalGuardedCertificatePreservation := by
  intro body typed positive tag window context hc α typ x y k
  let P := programGraph (guardedTyped typed tag) (suc z) ![numeral context,typ,x] ⊓
    programGraph (guardedPositive positive typed tag window) (suc z) ![numeral context,x,y,k]
  obtain ⟨d⟩ := certificateClosure (body := body) (Gamma := [P])
    typed positive tag window (numeral context) typ x y k
    (windowNumeral window context hc)
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
