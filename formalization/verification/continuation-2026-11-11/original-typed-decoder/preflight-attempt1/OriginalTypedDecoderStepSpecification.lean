module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderStepSpecification
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original arithmetic pair relation, used for every state and request
field below. No typed-decoder transition occurs in this specification. -/
def StepPair {alpha : Type} (code left right : OTerm alpha) : Formula alpha :=
  programGraph InternalPairing.pairing code ![left, right]

/-- The original nil-zero, successor-of-pair cons relation. This is also the
original arrow-type constructor when its arguments are domain and codomain. -/
def StepCons {alpha : Type} (code head tail : OTerm alpha) : Formula alpha :=
  programGraph InternalListCodec.consCode code ![head, tail]

/-- Both fields of the predecessor are retained even at zero. Branches below
explicitly reject zero before interpreting these fields as an arrow/list. -/
def StepArrowFields {alpha : Type} (code domain codomain : OTerm alpha) : Formula alpha :=
  existsOne
    (programGraph InternalEqualityTest.predecessor (.var (.inr 0))
        ![code.relabel Sum.inl] ⊓
      StepPair (.var (.inr 0)) (domain.relabel Sum.inl) (codomain.relabel Sum.inl))

/-- A literal request is pair(mode,pair(gamma,pair(type,raw))). All fields
are arbitrary arithmetic terms, not decoded source objects. -/
def StepRequest {alpha : Type}
    (request mode gamma typ raw : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 2)
    (StepPair (request.relabel Sum.inl) (mode.relabel Sum.inl)
        (.var (.inr (0 : Fin 2))) ⊓
      (StepPair (.var (.inr (0 : Fin 2))) (gamma.relabel Sum.inl)
          (.var (.inr (1 : Fin 2))) ⊓
        StepPair (.var (.inr (1 : Fin 2))) (typ.relabel Sum.inl) (raw.relabel Sum.inl)))

def StepLive {alpha : Type} (out work : OTerm alpha) : Formula alpha :=
  StepPair out (numeral 1) work

/-- Push exactly one literal request ahead of the unchanged work suffix. -/
def StepPushOne {alpha : Type}
    (out mode gamma typ raw rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 2)
    (StepRequest (.var (.inr (0 : Fin 2))) (mode.relabel Sum.inl)
        (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) ⊓
      (StepCons (.var (.inr (1 : Fin 2))) (.var (.inr (0 : Fin 2)))
          (rest.relabel Sum.inl) ⊓
        StepLive (out.relabel Sum.inl) (.var (.inr (1 : Fin 2)))))

/-- First request, then second request, then the SAME remaining work. -/
def StepPushTwo {alpha : Type}
    (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 4)
    (StepRequest (.var (.inr (0 : Fin 4))) (mode₁.relabel Sum.inl)
        (gamma₁.relabel Sum.inl) (typ₁.relabel Sum.inl) (raw₁.relabel Sum.inl) ⊓
      (StepRequest (.var (.inr (1 : Fin 4))) (mode₂.relabel Sum.inl)
          (gamma₂.relabel Sum.inl) (typ₂.relabel Sum.inl) (raw₂.relabel Sum.inl) ⊓
        (StepCons (.var (.inr (2 : Fin 4))) (.var (.inr (1 : Fin 4)))
            (rest.relabel Sum.inl) ⊓
          (StepCons (.var (.inr (3 : Fin 4))) (.var (.inr (0 : Fin 4)))
              (.var (.inr (2 : Fin 4))) ⊓
            StepLive (out.relabel Sum.inl) (.var (.inr (3 : Fin 4)))))))

/-- The common original payload pair(d,pair(first,second)). -/
def StepBinaryPayload {alpha : Type}
    (payload domain first second : OTerm alpha) : Formula alpha :=
  existsOne
    (StepPair (payload.relabel Sum.inl) (domain.relabel Sum.inl) (.var (.inr 0)) ⊓
      StepPair (.var (.inr 0)) (first.relabel Sum.inl) (second.relabel Sum.inl))

/-- All six original numbered fields, including the label, are preserved.
No equation identifies the recorded result type with the head's result. -/
def StepNumberedPayload {alpha : Type}
    (payload label head result base types extras : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 4)
    (StepPair (payload.relabel Sum.inl) (label.relabel Sum.inl)
        (.var (.inr (0 : Fin 4))) ⊓
      (StepPair (.var (.inr (0 : Fin 4))) (head.relabel Sum.inl)
          (.var (.inr (1 : Fin 4))) ⊓
        (StepPair (.var (.inr (1 : Fin 4))) (result.relabel Sum.inl)
            (.var (.inr (2 : Fin 4))) ⊓
          (StepPair (.var (.inr (2 : Fin 4))) (base.relabel Sum.inl)
              (.var (.inr (3 : Fin 4))) ⊓
            StepPair (.var (.inr (3 : Fin 4))) (types.relabel Sum.inl)
              (extras.relabel Sum.inl)))))

/-- Variable checking calls the unchanged original variable decoder at the
same requested type, payload index and context. Only exact output one accepts. -/
def StepVariable {alpha : Type} (out gamma typ index rest : OTerm alpha) : Formula alpha :=
  existsOne
    (OriginalVariableDecoder.graph (.var (.inr 0)) (typ.relabel Sum.inl)
        (index.relabel Sum.inl) (gamma.relabel Sum.inl) ⊓
      ((equal (.var (.inr 0)) (numeral 1) ⊓
          StepLive (out.relabel Sum.inl) (rest.relabel Sum.inl)) ⊔
        ((equal (.var (.inr 0)) (numeral 1)).not ⊓
          equal (out.relabel Sum.inl) (numeral 0))))

/-- Lambda requires a nonzero requested arrow whose domain matches the
literal raw domain. The body request extends the same original context. -/
def StepLambda {alpha : Type} (out gamma typ payload rest : OTerm alpha) : Formula alpha :=
  let v : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 5)
    (StepPair (payload.relabel Sum.inl) (v 0) (v 1) ⊓
      (StepArrowFields (typ.relabel Sum.inl) (v 2) (v 3) ⊓
        (StepCons (v 4) (v 0) (gamma.relabel Sum.inl) ⊓
          (((equal (typ.relabel Sum.inl) (numeral 0)).not ⊓
              (equal (v 2) (v 0) ⊓
                StepPushOne (out.relabel Sum.inl) (numeral 0) (v 4) (v 3) (v 1)
                  (rest.relabel Sum.inl))) ⊔
            ((equal (typ.relabel Sum.inl) (numeral 0) ⊔ (equal (v 2) (v 0)).not) ⊓
              equal (out.relabel Sum.inl) (numeral 0))))))

/-- Application visits the function at the literal arrow (d,requested type)
before its argument at d. No extra type, head or window test is introduced. -/
def StepApplication {alpha : Type}
    (out gamma typ payload rest : OTerm alpha) : Formula alpha :=
  let v : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 4)
    (StepBinaryPayload (payload.relabel Sum.inl) (v 0) (v 1) (v 2) ⊓
      (StepCons (v 3) (v 0) (typ.relabel Sum.inl) ⊓
        StepPushTwo (out.relabel Sum.inl)
          (numeral 0) (gamma.relabel Sum.inl) (v 3) (v 1)
          (numeral 0) (gamma.relabel Sum.inl) (v 0) (v 2) (rest.relabel Sum.inl)))

def StepBottom {alpha : Type} (out typ payload rest : OTerm alpha) : Formula alpha :=
  (equal payload typ ⊓ StepLive out rest) ⊔
    ((equal payload typ).not ⊓ equal out (numeral 0))

/-- The head decoder is arbitrary. Its actual output must be nonzero and its
result field must equal the requested type; its argument-type field is kept. -/
def StepOrdinary {alpha : Type} (H : Program 1)
    (out gamma typ payload rest : OTerm alpha) : Formula alpha :=
  let v : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 5)
    (StepPair (payload.relabel Sum.inl) (v 0) (v 1) ⊓
      (programGraph H (v 2) ![v 0] ⊓
        (StepArrowFields (v 2) (v 3) (v 4) ⊓
          (((equal (v 2) (numeral 0)).not ⊓
              (equal (v 3) (typ.relabel Sum.inl) ⊓
                StepPushOne (out.relabel Sum.inl) (numeral 1)
                  (gamma.relabel Sum.inl) (v 4) (v 1) (rest.relabel Sum.inl))) ⊔
            ((equal (v 2) (numeral 0) ⊔ (equal (v 3) (typ.relabel Sum.inl)).not) ⊓
              equal (out.relabel Sum.inl) (numeral 0))))))

/-- Numbered checking deliberately does NOT compare the head's result field
with the requested type. The original recorded result must match; base and
extra argument requests keep their separate original type lists and order. -/
def StepNumbered {alpha : Type} (H : Program 1)
    (out gamma typ payload rest : OTerm alpha) : Formula alpha :=
  let v : Fin 9 → OTerm (alpha ⊕ Fin 9) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 9)
    (StepNumberedPayload (payload.relabel Sum.inl)
        (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) ⊓
      (programGraph H (v 6) ![v 1] ⊓
        (StepArrowFields (v 6) (v 7) (v 8) ⊓
          (((equal (v 6) (numeral 0)).not ⊓
              (equal (v 2) (typ.relabel Sum.inl) ⊓
                StepPushTwo (out.relabel Sum.inl)
                  (numeral 1) (gamma.relabel Sum.inl) (v 8) (v 3)
                  (numeral 1) (gamma.relabel Sum.inl) (v 4) (v 5)
                  (rest.relabel Sum.inl))) ⊔
            ((equal (v 6) (numeral 0) ⊔ (equal (v 2) (typ.relabel Sum.inl)).not) ⊓
              equal (out.relabel Sum.inl) (numeral 0))))))

/-- Both nil metadata and the requested argument-type list must be zero. -/
def StepArgumentsNil {alpha : Type}
    (out typ payload rest : OTerm alpha) : Formula alpha :=
  ((equal payload (numeral 0) ⊓ equal typ (numeral 0)) ⊓ StepLive out rest) ⊔
    (((equal payload (numeral 0)).not ⊔ (equal typ (numeral 0)).not) ⊓
      equal out (numeral 0))

/-- Cons arguments check the recorded head type against the requested list,
then visit the term head before the argument tail, retaining the same gamma. -/
def StepArgumentsCons {alpha : Type}
    (out gamma typ payload rest : OTerm alpha) : Formula alpha :=
  let v : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 5)
    (StepBinaryPayload (payload.relabel Sum.inl) (v 0) (v 1) (v 2) ⊓
      (StepArrowFields (typ.relabel Sum.inl) (v 3) (v 4) ⊓
        (((equal (typ.relabel Sum.inl) (numeral 0)).not ⊓
            (equal (v 3) (v 0) ⊓
              StepPushTwo (out.relabel Sum.inl)
                (numeral 0) (gamma.relabel Sum.inl) (v 0) (v 1)
                (numeral 1) (gamma.relabel Sum.inl) (v 4) (v 2)
                (rest.relabel Sum.inl))) ⊔
          ((equal (typ.relabel Sum.inl) (numeral 0) ⊔ (equal (v 3) (v 0)).not) ⊓
            equal (out.relabel Sum.inl) (numeral 0)))))

/-- Arithmetic exclusion of every original constructor tag. -/
def StepUnknownTag {alpha : Type} (tag : OTerm alpha) : Formula alpha :=
  (equal tag (numeral 0)).not ⊓
    ((equal tag (numeral 1)).not ⊓
      ((equal tag (numeral 2)).not ⊓
        ((equal tag (numeral 3)).not ⊓
          ((equal tag (numeral 4)).not ⊓
            ((equal tag (numeral 5)).not ⊓
              ((equal tag (numeral 6)).not ⊓ (equal tag (numeral 7)).not))))))

/-- Explicit term-tag dispatch, including both forbidden argument tags and
every other raw tag. The six term cases expose their own rejecting outputs. -/
def StepTermDispatch {alpha : Type} (H : Program 1)
    (out gamma typ tag payload rest : OTerm alpha) : Formula alpha :=
  (equal tag (numeral 0) ⊓ StepVariable out gamma typ payload rest) ⊔
    ((equal tag (numeral 1) ⊓ StepLambda out gamma typ payload rest) ⊔
      ((equal tag (numeral 2) ⊓ StepApplication out gamma typ payload rest) ⊔
        ((equal tag (numeral 3) ⊓ StepBottom out typ payload rest) ⊔
          ((equal tag (numeral 4) ⊓ StepOrdinary H out gamma typ payload rest) ⊔
            ((equal tag (numeral 5) ⊓ StepNumbered H out gamma typ payload rest) ⊔
              ((equal tag (numeral 6) ⊓ equal out (numeral 0)) ⊔
                ((equal tag (numeral 7) ⊓ equal out (numeral 0)) ⊔
                  (StepUnknownTag tag ⊓ equal out (numeral 0)))))))))

/-- Explicit argument-tag dispatch. All six term tags and all unknown tags
reject, not merely the well-formed source constructors. -/
def StepArgumentsDispatch {alpha : Type}
    (out gamma typ tag payload rest : OTerm alpha) : Formula alpha :=
  (equal tag (numeral 0) ⊓ equal out (numeral 0)) ⊔
    ((equal tag (numeral 1) ⊓ equal out (numeral 0)) ⊔
      ((equal tag (numeral 2) ⊓ equal out (numeral 0)) ⊔
        ((equal tag (numeral 3) ⊓ equal out (numeral 0)) ⊔
          ((equal tag (numeral 4) ⊓ equal out (numeral 0)) ⊔
            ((equal tag (numeral 5) ⊓ equal out (numeral 0)) ⊔
              ((equal tag (numeral 6) ⊓ StepArgumentsNil out typ payload rest) ⊔
                ((equal tag (numeral 7) ⊓ StepArgumentsCons out gamma typ payload rest) ⊔
                  (StepUnknownTag tag ⊓ equal out (numeral 0)))))))))

/-- The request mode is itself checked arithmetically; unknown modes reject. -/
def StepModeDispatch {alpha : Type} (H : Program 1)
    (out mode gamma typ tag payload rest : OTerm alpha) : Formula alpha :=
  (equal mode (numeral 0) ⊓ StepTermDispatch H out gamma typ tag payload rest) ⊔
    ((equal mode (numeral 1) ⊓ StepArgumentsDispatch out gamma typ tag payload rest) ⊔
      (((equal mode (numeral 0)).not ⊓ (equal mode (numeral 1)).not) ⊓
        equal out (numeral 0)))

/-- Open the same actual first work request and its raw constructor. Every
field is quantified internally using only original pair and list relations. -/
def StepNonemptyWork {alpha : Type} (H : Program 1)
    (out work : OTerm alpha) : Formula alpha :=
  let v : Fin 8 → OTerm (alpha ⊕ Fin 8) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 8)
    (StepCons (work.relabel Sum.inl) (v 0) (v 1) ⊓
      (StepRequest (v 0) (v 2) (v 3) (v 4) (v 5) ⊓
        (StepPair (v 5) (v 6) (v 7) ⊓
          StepModeDispatch H (out.relabel Sum.inl)
            (v 2) (v 3) (v 4) (v 6) (v 7) (v 1))))

/-- Independent all-input, all-output arithmetic one-step specification.
Non-live states return zero. A live empty state is unchanged. A live nonempty
state performs the literal mode/tag dispatch above. H is completely arbitrary;
no native calibration, decoded typing judgment or successful run is a premise.
In particular, this is NOT the graph of the new transition under another name. -/
def stepSpec {alpha : Type} (H : Program 1) (out input : OTerm alpha) : Formula alpha :=
  let v : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
  InternalFiniteBlocks.block (k := 2)
    (StepPair (input.relabel Sum.inl) (v 0) (v 1) ⊓
      (((equal (v 0) (numeral 1)).not ⊓ equal (out.relabel Sum.inl) (numeral 0)) ⊔
        (equal (v 0) (numeral 1) ⊓
          ((equal (v 1) (numeral 0) ⊓ equal (out.relabel Sum.inl) (input.relabel Sum.inl)) ⊔
            ((equal (v 1) (numeral 0)).not ⊓
              StepNonemptyWork H (out.relabel Sum.inl) (v 1))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderStepSpecification
