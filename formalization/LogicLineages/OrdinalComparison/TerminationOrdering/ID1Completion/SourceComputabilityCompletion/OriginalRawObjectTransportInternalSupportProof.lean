module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Auxiliary queries expose coordinates of the frozen wrapper; they are not
new source selectors or replacements for any calibrated final-tuple Program. -/
def sourceContext : Program 2 := leftOf (.projection 1)
def sourcePacked : Program 2 := rightOf (.projection 1)
def extendedContext : Program 2 := consOf (.projection 0) sourceContext
def shiftedPayload : Program 2 := .composition shiftPackedRaw ![constant 2 0,sourcePacked]
def shiftQueries : Fin 4 → Program 2 :=
  ![sourceContext,sourcePacked,extendedContext,shiftedPayload]

def erasedContext : Program 1 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left)
def erasedDomain : Program 1 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => InternalUnpair.left)
def erasedPayload : Program 1 :=
  .composition erasePackedRaw ![erasedDomain,constant 1 0,InternalUnpair.right]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Original unpair reverse-inverse recovers the SAME supplied input Object. -/
theorem shiftRecoveredAt (d input shifted : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (hs : ∀ i, Nonempty (Derivation body Delta
      (programGraph (shiftQueries i) (ys i) (Fin.cons d (Fin.cons input Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input))) :
    Nonempty (Derivation body Delta
      (ShiftRecovered d input shifted (ys 0) (ys 1) (ys 2) (ys 3))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons d (Fin.cons input Fin.elim0)
  have hl := unaryRecover InternalUnpair.left (.projection 1) (ys 0) input xs
    (hs 0) (projectionValue 1 xs)
  have hr := unaryRecover InternalUnpair.right (.projection 1) (ys 1) input xs
    (hs 1) (projectionValue 1 xs)
  have hp := reconstructPair input (ys 0) (ys 1) hl hr
  have hc := binaryRecover InternalListCodec.consCode (.projection 0) sourceContext
    (ys 2) d (ys 0) xs (hs 2) (projectionValue 0 xs) (hs 0)
  have ht := binaryRecover shiftPackedRaw (constant 2 0) sourcePacked
    (ys 3) (numeral 0) (ys 1) xs (hs 3) (constantValue 0 xs) (hs 1)
  have hp' := binaryRecover InternalPairing.pairing extendedContext shiftedPayload
    shifted (ys 2) (ys 3) xs ho (hs 2) (hs 3)
  exact andIntro hp (andIntro hc (andIntro ht hp'))

/-- The context head/tail are justified by an actual original cons graph. -/
theorem eraseComponents (d input gamma packed extendedGamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input extendedGamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extendedGamma d gamma))) :
    Nonempty (Derivation body Delta (graph1 erasedContext gamma input)) ∧
    (∀ i : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![erasedDomain,constant 1 0,InternalUnpair.right] : Fin 3 → Program 1) i)
        ((![d,numeral 0,packed] : Fin 3 → OTerm alpha) i) (Fin.cons input Fin.elim0)))) := by
  have hd := InternalListCodecSupportProof.consDestruction extendedGamma d gamma hc
  have hh := andLeft hd
  have ht := andLeft (andRight hd)
  have hl := pairLeft input extendedGamma packed hp
  have hr := pairRight input extendedGamma packed hp
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  refine ⟨unaryValue InternalListCodec.tailCode InternalUnpair.left gamma extendedGamma xs ht hl,?_⟩
  have hhead := unaryValue InternalListCodec.headCode InternalUnpair.left d extendedGamma xs hh hl
  intro i
  exact Fin.cases hhead (Fin.cases (constantValue 0 xs)
    (Fin.cases hr (fun q => Fin.elim0 q))) i

theorem eraseRecoveredAt (d input erased gamma packed extendedGamma erasedPacked : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input extendedGamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extendedGamma d gamma)))
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)))
    (hq : Nonempty (Derivation body Delta (graph1 erasedPayload erasedPacked input))) :
    Nonempty (Derivation body Delta
      (EraseRecovered d input erased gamma packed extendedGamma erasedPacked)) := by
  have hs := eraseComponents d input gamma packed extendedGamma hp hc
  have ht := compositionRecover erasePackedRaw ![erasedDomain,constant 1 0,InternalUnpair.right]
    erasedPacked (Fin.cons input Fin.elim0)
    (Fin.cons d (Fin.cons (numeral 0) (Fin.cons packed Fin.elim0))) hq hs.2
  have ho := binaryRecover InternalPairing.pairing erasedContext erasedPayload
    erased gamma erasedPacked (Fin.cons input Fin.elim0) he hs.1 hq
  exact andIntro hp (andIntro hc (andIntro ht ho))

/-- Reverse construction uses the SAME raw payload, domain and tail context. -/
theorem eraseObjectBackward (d input erased gamma packed extendedGamma erasedPacked : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input extendedGamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extendedGamma d gamma)))
    (ht : Nonempty (Derivation body Delta
      (graph3 erasePackedRaw erasedPacked d (numeral 0) packed)))
    (ho : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing erased gamma erasedPacked))) :
    Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)) := by
  have hs := eraseComponents d input gamma packed extendedGamma hp hc
  have hq := compositionValue erasePackedRaw ![erasedDomain,constant 1 0,InternalUnpair.right]
    erasedPacked (Fin.cons input Fin.elim0)
    (Fin.cons d (Fin.cons (numeral 0) (Fin.cons packed Fin.elim0))) ht hs.2
  exact binaryValue InternalPairing.pairing erasedContext erasedPayload erased gamma erasedPacked
    (Fin.cons input Fin.elim0) ho hs.1 hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSupportProof
