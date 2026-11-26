module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalHereditaryValidity OriginalHereditaryValidityInternalRecurrence
open OriginalTransparentLambdaValidity

/-- A literal original raw tag, with no decoding, typing or validity test. -/
def TagIs {alpha : Type} (tag : Nat) (raw : OTerm alpha) : Formula alpha :=
  graph1 OriginalLambdaConstructor.tag (numeral tag) raw

/-- Exact zero/one output for a specified arithmetic acceptance formula.
The negative branch includes all failures, not only a supplied zero output. -/
def BooleanOutput {alpha : Type} (out : OTerm alpha) (accepted : Formula alpha) :
    Formula alpha :=
  (equal out (numeral 1) ⊓ accepted) ⊔
    (equal out OrdinaryArithmetic.zeroTerm ⊓ accepted.not)

/-- The original binary codomain selector first reads the ACTUAL outer type,
then takes the original successor/pair-list tail. This is total at type zero
and at malformed inputs; no successful arrow decoding is assumed. -/
def CodomainGraph {alpha : Type} (codomain raw : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (graph1 InternalUnpair.left (.var (.inr (0 : Fin 1))) (raw.relabel Sum.inl) ⊓
      graph1 InternalListCodec.tailCode (codomain.relabel Sum.inl)
        (.var (.inr (0 : Fin 1))))

/-- Exact original lambda shape. The outer type, payload domain and outer
type's codomain are all obtained INTERNALLY from the SAME raw value. The
arrow graph asserts outer = succ(pair domain codomain), so outer type zero
and domain mismatch reject even when the raw tag is one. -/
def LambdaShape {alpha : Type} (raw : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 3)
    (graph1 InternalUnpair.left (.var (.inr (0 : Fin 3))) (raw.relabel Sum.inl) ⊓
      (graph1 OriginalLambdaConstructor.domain (.var (.inr (1 : Fin 3)))
          (raw.relabel Sum.inl) ⊓
        (graph1 InternalListCodec.tailCode (.var (.inr (2 : Fin 3)))
            (.var (.inr (0 : Fin 3))) ⊓
          graph2 OriginalLambdaConstructor.arrow (.var (.inr (0 : Fin 3)))
            (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3))))))

/-- The source lambda callback pays shape plus BOTH original memberships,
at the same supplied runtime parameter. All three type-number witnesses
are internal. No body validity, source acceptance or window closure is
hidden in this root-only formula. -/
def SourceLambdaRootFactors {alpha : Type} (data : Data)
    (raw parameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 3)
    (graph1 InternalUnpair.left (.var (.inr (0 : Fin 3))) (raw.relabel Sum.inl) ⊓
      (graph1 OriginalLambdaConstructor.domain (.var (.inr (1 : Fin 3)))
          (raw.relabel Sum.inl) ⊓
        (graph1 InternalListCodec.tailCode (.var (.inr (2 : Fin 3)))
            (.var (.inr (0 : Fin 3))) ⊓
          (graph2 OriginalLambdaConstructor.arrow (.var (.inr (0 : Fin 3)))
              (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3))) ⊓
            (graph2 data.member (numeral 1) (.var (.inr (0 : Fin 3)))
                (parameter.relabel Sum.inl) ⊓
              graph2 data.member (numeral 1) (.var (.inr (1 : Fin 3)))
                (parameter.relabel Sum.inl))))))

/-- Full output of the literal sourceRoot AST for arbitrary Data. Tag two
returns one; tag one has exactly the original shape and membership tests;
every other tag retains the WHOLE original oldSource output, including
arbitrary non-Boolean outputs. This formula is not a replacement validator. -/
def SourceRootOutput {alpha : Type} (data : Data)
    (out raw parameter : OTerm alpha) : Formula alpha :=
  (TagIs 2 raw ⊓ equal out (numeral 1)) ⊔
    ((TagIs 1 raw ⊓ BooleanOutput out (SourceLambdaRootFactors data raw parameter)) ⊔
      ((TagIs 2 raw).not ⊓
        ((TagIs 1 raw).not ⊓ graph2 data.oldSource out raw parameter)))

/-- The target callback has NO membership filter. Its opaque-root branch
retains the complete oldTarget output, not merely its acceptance predicate. -/
def TargetRootOutput {alpha : Type} (data : Data)
    (out raw parameter : OTerm alpha) : Formula alpha :=
  (TagIs 2 raw ⊓ equal out (numeral 1)) ⊔
    ((TagIs 1 raw ⊓ BooleanOutput out (LambdaShape raw)) ⊔
      ((TagIs 2 raw).not ⊓
        ((TagIs 1 raw).not ⊓ graph2 data.oldTarget out raw parameter)))

/-- A literal original lambda, with the ACTUAL repacked body and outer arrow
internally witnessed. Fields fixes its tag, type, domain and body selector;
the constructor graph reconstructs this SAME raw code. There is no body
typing or body acceptance premise. The body is packed at the outer codomain. -/
def LiteralLambda {alpha : Type} (raw : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 4)
    (OriginalLambdaConstructor.Fields (raw.relabel Sum.inl)
        (.var (.inr (0 : Fin 4))) (.var (.inr (1 : Fin 4)))
        (.var (.inr (2 : Fin 4))) (.var (.inr (3 : Fin 4))) ⊓
      graph3 OriginalLambdaConstructor.constructor (raw.relabel Sum.inl)
        (.var (.inr (0 : Fin 4))) (.var (.inr (1 : Fin 4)))
        (.var (.inr (2 : Fin 4))))

/-- Lambda recurrence factors for LOCAL HS = sourceValidator rawData.
N is exactly normalizedData rawData, not a later chosen final Data tuple.
RootLambdaChild opens the original initial state, actual repacked body and
actual childParameter INTERNALLY. It retains the raw outer context and
conses the actual domain onto encoded Gamma, then calls the IDENTICAL HS
at that child's OWN payload+1 fuel. Body acceptance is a conclusion factor,
not a supplied premise. The target callback is the same targetRoot N. -/
def SourceLambdaFactors {alpha : Type} (rawData : Data)
    (raw parameter : OTerm alpha) : Formula alpha :=
  let N := normalizedData rawData
  SourceLambdaRootFactors N raw parameter ⊓
    RootLambdaChild (sourceRoot N) (targetRoot N) N.member raw parameter

/-- Lambda recurrence factors for LOCAL HT = targetValidator rawData.
Both auxiliary callbacks remain constant one. No source-window membership
or source acceptance is introduced, including at the actual lambda body. -/
def TargetLambdaFactors {alpha : Type} (rawData : Data)
    (raw parameter : OTerm alpha) : Formula alpha :=
  let N := normalizedData rawData
  LambdaShape raw ⊓
    RootLambdaChild (targetRoot N) (InternalLessThan.constantOne 2)
      (InternalLessThan.constantOne 2) raw parameter

/- FROZEN INDEPENDENT INTERNAL SPECIFICATION, NOT A PROOF.

Root/shape/constructor laws follow the literal AST and original arithmetic
pair/list graph laws, without evaluating a native function. The local HS/HT
lambda recurrence contracts await the independent arbitrary-callback
OriginalHereditaryValidityInternalRecurrence packet. The bottom contracts
use exact-bottom shape, the normalized ORIGINAL leaves captured in N, and
the same framed validator; no native calibration is an internal reflection
principle. All raw Data, raw contexts and encoded Gamma codes are arbitrary.

These are local transparent-validator laws only. Transport through later
bottom/member normalization and the final application fold, final source
lambda closure, canonical-body coherence, lambda/substitution computability
and retention of the complete global Package remain separate obligations. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternal
