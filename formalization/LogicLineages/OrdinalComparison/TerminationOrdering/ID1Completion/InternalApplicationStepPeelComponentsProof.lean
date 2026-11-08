module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Four literal original pair graphs introduce the original packed application. -/
theorem packedAtPairs (d e fp ap children nodeBody node out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing children fp ap)))
    (hb : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nodeBody d children)))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing node positionTerm nodeBody)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out e node))) :
    Nonempty (Derivation body Gamma (graph4 packedApplication out d e fp ap)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  have ch := binaryValue InternalPairing.pairing (.projection 2) (.projection 3)
    children fp ap xs hc (projectionValue 2 xs) (projectionValue 3 xs)
  have bd := binaryValue InternalPairing.pairing (.projection 0)
    (pairOf (.projection 2) (.projection 3)) nodeBody d children xs hb (projectionValue 0 xs) ch
  have nd := binaryValue InternalPairing.pairing (two 4)
    (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))) node positionTerm nodeBody xs hn
    (twoValue xs) bd
  exact binaryValue InternalPairing.pairing (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    out e node xs ho (projectionValue 1 xs) nd

/-- Concrete field graphs, retaining the original numeric payload witnesses. -/
theorem fieldsAtPairs (p : Program 1) (state out d e fp ap children nodeBody node : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 p out state)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing children fp ap)))
    (hb : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nodeBody d children)))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing node positionTerm nodeBody)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out e node))) :
    Nonempty (Derivation body Gamma
      (graph1 (outerType p) e state ⊓
        (graph1 (constructorTag p) positionTerm state ⊓
          (graph1 (appDomain p) d state ⊓
            (graph1 (functionPayload p) fp state ⊓ graph1 (argumentPayload p) ap state))))) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have nd := unaryValue InternalUnpair.right p node out xs (pairRight out e node ho) hp
  have bd := unaryValue InternalUnpair.right (rightOf p) nodeBody node xs
    (pairRight node positionTerm nodeBody hn) nd
  have ch := unaryValue InternalUnpair.right (appBody p) children nodeBody xs
    (pairRight nodeBody d children hb) bd
  exact andIntro (unaryValue InternalUnpair.left p e out xs (pairLeft out e node ho) hp)
    (andIntro (unaryValue InternalUnpair.left (rightOf p) positionTerm node xs
      (pairLeft node positionTerm nodeBody hn) nd)
      (andIntro (unaryValue InternalUnpair.left (appBody p) d nodeBody xs
        (pairLeft nodeBody d children hb) bd)
        (andIntro (unaryValue InternalUnpair.left (rightOf (appBody p)) fp children xs
          (pairLeft children fp ap hc) ch)
          (unaryValue InternalUnpair.right (rightOf (appBody p)) ap children xs
            (pairRight children fp ap hc) ch))))

theorem endpointTypesAccept (d e arrow s t a : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow s)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow t)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a))) :
    Nonempty (Derivation body Gamma (graph5 endpointTypeGuard (suc z) d e s t a)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))
  have ar := binaryValue InternalListCodec.consCode (.projection 0) (.projection 1) arrow d e xs
    har (projectionValue 0 xs) (projectionValue 1 xs)
  apply conjunctionAccept _ _ xs
  · exact sameAccept _ _ arrow xs
      (unaryValue InternalUnpair.left (.projection 2) arrow s xs hs (projectionValue 2 xs)) ar
  · apply conjunctionAccept _ _ xs
    · exact sameAccept _ _ arrow xs
        (unaryValue InternalUnpair.left (.projection 3) arrow t xs ht (projectionValue 3 xs)) ar
    · exact sameAccept _ _ d xs
        (unaryValue InternalUnpair.left (.projection 4) d a xs ha (projectionValue 4 xs))
        (projectionValue 0 xs)

theorem nonemptyAccept (state prefixed path : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 rawPath prefixed state)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode prefixed positionTerm path))) :
    Nonempty (Derivation body Gamma (graph1 nonemptyPath (suc z) state)) := by
  have hd := InternalListCodecSupportProof.consDestruction prefixed positionTerm path hc
  have hn := andRight (andRight hd)
  exact branchValue rawPath (InternalAcceptance.constantZero 1) (InternalLessThan.constantOne 1)
    (suc z) prefixed z (suc z) (Fin.cons state Fin.elim0) hp
    (constantZeroValue _) (InternalLessThanSupportProof.oneConstantValue _)
    (InternalControlGraphProof.conditionalAtNonzero prefixed z (suc z) hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
