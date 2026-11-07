module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GammaGuardedSource GammaGuardedSourceGraphSupportProof GuardedSourceGraphSupportProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem certificateWithXY (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (a b c typ x y u k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hy : Nonempty (Derivation body Gamma (programGraph gamma b ![y])))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u])) := by
  apply programCases gamma ![u] _
  intro β j Delta d hj hd
  simp only [programRename,sucRelabel,zRelabel,tupleTwoRename]
  have hx' := renameInto hx j Delta hj
  have hy' := renameInto hy j Delta hj
  have ht' := renameInto ht j Delta hj
  have hp' := renameInto hp j Delta hj
  have hg' := renameInto hg j Delta hj
  simp only [programRename,sucRelabel,zRelabel,tupleOneRename,tupleTwoRename,
    tupleThreeRename,tupleFourRename] at hx' hy' ht' hp' hg' hd
  exact certificateAtValues typed positive valid gamma tag window
    (a.relabel j) (b.relabel j) d (c.relabel j) (typ.relabel j)
    (x.relabel j) (y.relabel j) (u.relabel j) (k.relabel j) hx' hy' hd ht' hp' hg'

theorem certificateWithX (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (a c typ x y u k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u])) := by
  apply programCases gamma ![y] _
  intro β j Delta b hj hb
  simp only [programRename,sucRelabel,zRelabel,tupleTwoRename]
  have hx' := renameInto hx j Delta hj
  have ht' := renameInto ht j Delta hj
  have hp' := renameInto hp j Delta hj
  have hg' := renameInto hg j Delta hj
  simp only [programRename,sucRelabel,zRelabel,tupleOneRename,tupleTwoRename,
    tupleThreeRename,tupleFourRename] at hx' ht' hp' hg' hb
  exact certificateWithXY typed positive valid gamma tag window
    (a.relabel j) b (c.relabel j) (typ.relabel j)
    (x.relabel j) (y.relabel j) (u.relabel j) (k.relabel j) hx' hb ht' hp' hg'

/-- All three Gamma values come from ORIGINAL Program totality and are aligned
by graph functionality. No window validity assumption occurs. -/
theorem certificateTransport (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (c typ x y u k : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u])) := by
  apply programCases gamma ![x] _
  intro β j Delta a hj ha
  simp only [programRename,sucRelabel,zRelabel,tupleTwoRename]
  have ht' := renameInto ht j Delta hj
  have hp' := renameInto hp j Delta hj
  have hg' := renameInto hg j Delta hj
  simp only [programRename,sucRelabel,zRelabel,tupleOneRename,tupleTwoRename,
    tupleThreeRename,tupleFourRename] at ht' hp' hg' ha
  exact certificateWithX typed positive valid gamma tag window
    a (c.relabel j) (typ.relabel j)
    (x.relabel j) (y.relabel j) (u.relabel j) (k.relabel j) ha ht' hp' hg'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCertificateProof
