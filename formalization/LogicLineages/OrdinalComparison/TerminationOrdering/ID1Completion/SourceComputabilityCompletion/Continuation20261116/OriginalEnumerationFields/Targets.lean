module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Source Fields exactly, with actual original type/head/list/raw-Code encodings.
Boolean range and malformed behavior are separate universal contracts below. -/
def NativeOriginal : Prop := ∀ (n : Nat) (S : List Source.Ty)
    (H : List (NumberedAuxiliaryCoding.HeadCode (Fin n)))
    (labels tupleBound variableBound : Nat) (c : NumberedAuxiliaryCoding.Code (Fin n)),
  (evaluate (fields n) (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber c,
    variableBound,Encodable.encode S,Encodable.encode H,labels,tupleBound]) = 1 ↔
   NumberedAuxiliaryEnumeration.Fields S H labels tupleBound variableBound c)
def NativeBoolean : Prop := ∀ (n : Nat) (v : List.Vector Nat 6),
  evaluate (fields n) v = 0 ∨ evaluate (fields n) v = 1
def NativeMalformed : Prop := ∀ (n : Nat) (v : List.Vector Nat 6),
  NumberedNumericDecoding.decodeCode n (v.get 0) = none → evaluate (fields n) v = 0

def accepted {alpha : Type} (n : Nat) (raw variableBound types heads labels tupleBound : OTerm alpha) : Formula alpha :=
  programGraph (fields n) (numeral 1) ![raw,variableBound,types,heads,labels,tupleBound]
def valid {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw
/-- Membership stays in original encoded heads; raw conversion is explicitly witnessed.
All-raw invalid encoded heads retain the existing conversion-to-zero behavior. -/
def headAllowed {alpha : Type} (n : Nat) (heads rawHead : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 contains (numeral 1) (heads.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⊓
      graph1 (OriginalEncodedHeadConversion.convert n) (rawHead.relabel Sum.inl) (.var (.inr 0)))
/-- Actual list length and every actual entry, not membership in an opaque enumeration. -/
def typesAllowed {alpha : Type} (types allowed tupleBound : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (OriginalContextInsertion.lengthGraph (.var (.inr (0 : Fin 1))) (types.relabel Sum.inl) ⊓
      InternalLessThan.strictLess (.var (.inr 0)) (suc (tupleBound.relabel Sum.inl))) ⊓
    OriginalTypeListsMembership.Targets.allMembers types allowed

/-- Internal boolean range on all raw arguments, without a native truth premise. -/
def InternalBoolean : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (xs : Fin 6 → OTerm alpha) (out : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (fields n) out xs)) →
  Nonempty (Derivation body Delta (eqn out (numeral 0) ⊔ eqn out (numeral 1)))
def InternalMalformed : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 0) raw)) →
  Nonempty (Derivation body Delta
    (programGraph (fields n) (numeral 0) ![raw,b,S,H,labels,tupleBound]))

/-- Actual original variable branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalVariable : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound index : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (InternalLessThan.strictLess index b))))

/-- Actual original lambda branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalLambda : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound typ child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw typ child)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (graph2 contains (numeral 1) S typ ⊓ accepted n child (suc b) S H labels tupleBound))))

/-- Actual original application branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalApplication : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound typ left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw typ left right)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (graph2 contains (numeral 1) S typ ⊓ accepted n left b S H labels tupleBound ⊓ accepted n right b S H labels tupleBound))))

/-- Actual original bottom branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalBottom : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound typ : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw typ)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (graph2 contains (numeral 1) S typ))))

/-- Actual original ordinary branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound head child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (headAllowed n H head ⊓ accepted n child b S H labels tupleBound))))

/-- Actual original numbered branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalNumbered : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound label head typ base types extra : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,base,types,extra])) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (InternalLessThan.strictLess label (suc labels) ⊓ headAllowed n H head ⊓ graph2 contains (numeral 1) S typ ⊓ accepted n base b S H labels tupleBound ⊓ typesAllowed types S tupleBound ⊓ accepted n extra b S H labels tupleBound))))

/-- Actual original nil branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalNil : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound  : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw)))

/-- Actual original cons branch. Validity is explicit on arbitrary raw constructor inputs. -/
def InternalCons : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw b S H labels tupleBound typ left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)) →
  (Nonempty (Derivation body Delta (accepted n raw b S H labels tupleBound)) ↔
   Nonempty (Derivation body Delta (valid n raw ⊓ (graph2 contains (numeral 1) S typ ⊓ accepted n left b S H labels tupleBound ⊓ accepted n right b S H labels tupleBound))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
