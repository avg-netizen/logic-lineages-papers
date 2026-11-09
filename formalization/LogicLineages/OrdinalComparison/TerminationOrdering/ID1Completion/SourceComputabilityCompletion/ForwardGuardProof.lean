module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof GammaGuardedSource GammaGuardedSourceSyntaxProof
open GammaGuardedSourceGraphSupportProof GammaGuardedSourceBranchProof
open GuardedSourceGraphSupportProof GuardedSourceSyntaxProof
open InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original three decoder outputs are aligned inside the calculus.
Target typedness, rather than an inferred semantic validity claim, supplies
the target-object validity factor. -/
theorem certificateAtValues (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (a b d c typ x y u k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hy : Nonempty (Derivation body Gamma (programGraph gamma b ![y])))
    (hu : Nonempty (Derivation body Gamma (programGraph gamma d ![u])))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,y])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u])) := by
  have hvy := typedValid typed valid tag c typ y ht
  have hp' := guardedPositiveRecover (basePositive positive gamma) (baseTyped typed valid) tag window _ hp
  obtain ⟨hexy⟩ := positiveGamma positive gamma a b c x y k hx hy hp'
  obtain ⟨dgu⟩ := guardRecover valid gamma a d x u hx hu hg
  exact guardAccept valid gamma b d y u hy hu hvy
    ⟨Derivation.conjunctionLeft dgu⟩ ⟨trans (symm hexy) (Derivation.conjunctionRight dgu)⟩

theorem certificateWithXY (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (a b c typ x y u k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hy : Nonempty (Derivation body Gamma (programGraph gamma b ![y])))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,y])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u])) := by
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
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,y])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u])) := by
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

theorem certificateTransport (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (c typ x y u k : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,y])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u])) := by
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

theorem relationTransport (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (context : Nat) (typ x y u : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (GuardedSource.literalTyped (computability oldComp valid gamma tag) context typ y)))
    (hr : Nonempty (Derivation body Gamma
      (GuardedSource.literalR (source oldSource oldComp.typed valid gamma tag window) context x y)))
    (hg : Nonempty (Derivation body Gamma
      (literalGuard (computability oldComp valid gamma tag) x u))) :
    Nonempty (Derivation body Gamma
      (literalGuard (computability oldComp valid gamma tag) y u)) := by
  rw [literalTypedGraph] at ht
  rw [literalGuardGraph] at hg ⊢
  rw [literalRGraph] at hr
  obtain ⟨dr⟩ := hr
  let P : Formula (α ⊕ Fin 1) := programGraph
    (GuardedSource.guardedPositive (basePositive oldSource.positive gamma)
      (baseTyped oldComp.typed valid) tag window) (suc z)
    ![numeral context,x.relabel Sum.inl,y.relabel Sum.inl,.var (.inr 0)]
  let Delta := P :: Gamma.map weaken
  have ht' := renameInto ht Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have hg' := renameInto hg Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [programRename,sucRelabel,zRelabel,tupleTwoRename,tupleThreeRename,numeralRename] at ht' hg'
  have h := certificateTransport oldComp.typed oldSource.positive valid gamma tag window
    (numeral context) (typ.relabel Sum.inl) (x.relabel Sum.inl) (y.relabel Sum.inl)
    (u.relabel Sum.inl) (.var (.inr 0)) ht'
    (show Nonempty (Derivation body Delta P) from ⟨Derivation.hypothesis List.mem_cons_self⟩) hg'
  have hd : Nonempty (Derivation body Delta (weaken
      (programGraph (computability oldComp valid gamma tag).guard (suc z) ![y,u]))) := by
    simpa only [computability,baseComputability,GuardedSource.computability,weaken,
      programRename,sucRelabel,zRelabel,tupleTwoRename] using h
  obtain ⟨dd⟩ := hd
  exact ⟨Derivation.existentialElimination dr dd⟩

theorem actualOriginalForwardGuardTransport :
    ForwardGuardTargets.ActualOriginalForwardGuardTransport := by
  intro oldSource oldComp valid gamma tag window context α typ x y u
  let src := source oldSource oldComp.typed valid gamma tag window
  let comp := computability oldComp valid gamma tag
  let P := ((GuardedSource.literalTyped comp context typ y ⊓ GuardedSource.literalR src context x y) ⊓
    literalGuard comp x u)
  have h : Derivation (SourcePresentation.sourceBody src context) [P] P :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := relationTransport oldSource oldComp valid gamma tag window context typ x y u
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardProof
