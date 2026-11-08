module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationValidityStackAppend InternalApplicationValidityClosure
open InternalApplicationValidityClosureApplicationCoreProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Query coordinates are [domain,codomain,functionPayload,argumentPayload,
arrow,function,argument,parent]. All witnesses are supplied by original
internal Program totality and discharged before the final conclusion. -/
def childrenQ : Program 8 := pairOf (.projection 2) (.projection 3)
def middleQ : Program 8 := pairOf (.projection 0) childrenQ
def payloadQ : Program 8 := pairOf (two 8) middleQ
def packedQ : Program 8 := pairOf (.projection 1) payloadQ
def fnWorkQ : Program 8 := consOf (.projection 5) (InternalAcceptance.constantZero 8)
def argWorkQ : Program 8 := consOf (.projection 6) (InternalAcceptance.constantZero 8)
def joinedQ : Program 8 := consOf (.projection 5) argWorkQ
def parentWorkQ : Program 8 := consOf (.projection 7) (InternalAcceptance.constantZero 8)
def parentStateQ : Program 8 := pairOf (InternalLessThan.constantOne 8) parentWorkQ
def expandedStateQ : Program 8 := pairOf (InternalLessThan.constantOne 8) joinedQ
def queries : Fin 10 → Program 8 :=
  ![childrenQ,middleQ,payloadQ,packedQ,fnWorkQ,argWorkQ,joinedQ,parentWorkQ,
    parentStateQ,expandedStateQ]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationFromQueries (node leaf : Program 1)
    (arrow d e fp ap fn arg parent : OTerm α) (ys : Fin 10 → OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hfnValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) fn)))
    (hargValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) arg)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow
        (Fin.cons fn (Fin.cons arg (Fin.cons parent Fin.elim0))))))))))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  let xs : Fin 8 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow
      (Fin.cons fn (Fin.cons arg (Fin.cons parent Fin.elim0)))))))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) fp ap xs (hq 0) (projectionValue 2 xs) (projectionValue 3 xs)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) childrenQ
    (ys 1) d (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hp := binaryRecover InternalPairing.pairing (two 8) middleQ
    (ys 2) successState (ys 1) xs (hq 2) (twoValue xs) (hq 1)
  have hpp := binaryRecover InternalPairing.pairing (.projection 1) payloadQ
    (ys 3) e (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
  have hpacked := packedAtPairs d e fp ap (ys 0) (ys 1) (ys 2) (ys 3) hc hm hp hpp
  have he := valueUnique packedApplication (ys 3) parent
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) hpacked hparent
  have hparentPair := outputTransport InternalPairing.pairing (ys 3) parent
    (Fin.cons e (Fin.cons (ys 2) Fin.elim0)) he hpp
  have hfw := binaryRecover InternalListCodec.consCode (.projection 5)
    (InternalAcceptance.constantZero 8) (ys 4) fn z xs (hq 4)
    (projectionValue 5 xs) (constantZeroValue xs)
  have haw := binaryRecover InternalListCodec.consCode (.projection 6)
    (InternalAcceptance.constantZero 8) (ys 5) arg z xs (hq 5)
    (projectionValue 6 xs) (constantZeroValue xs)
  have hj := binaryRecover InternalListCodec.consCode (.projection 5) argWorkQ
    (ys 6) fn (ys 5) xs (hq 6) (projectionValue 5 xs) (hq 5)
  have hpw := binaryRecover InternalListCodec.consCode (.projection 7)
    (InternalAcceptance.constantZero 8) (ys 7) parent z xs (hq 7)
    (projectionValue 7 xs) (constantZeroValue xs)
  have hps := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 8) parentWorkQ
    (ys 8) (suc z) (ys 7) xs (hq 8) (InternalLessThanSupportProof.oneConstantValue xs) (hq 7)
  have hes := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 8) joinedQ
    (ys 9) (suc z) (ys 6) xs (hq 9) (InternalLessThanSupportProof.oneConstantValue xs) (hq 6)
  exact applicationAtValues node leaf d e fp ap arrow fn arg parent
    (ys 0) (ys 1) (ys 2) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9)
    harrow hfn harg hparent hc hm hp hparentPair hfw haw hj hpw hps hes
    hnode hfnValid hargValid

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationQueryProof
