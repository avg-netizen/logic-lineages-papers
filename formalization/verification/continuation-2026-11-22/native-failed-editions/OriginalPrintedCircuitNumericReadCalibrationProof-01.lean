module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadEffectiveProof
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawNotationCode
import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
open OrdinalComparison FieldComparison
open NaturalAffineGateGraph (Expression)
open OriginalNaturalFieldGates (IdentityDomain identityRead)
open OriginalPrintedCircuitSequential (Gate baseResult fieldResult)

private theorem allAffine (values : List Nat) (e : Expression) (out : Nat) :
    parser (values,encodeGate (Gate.base (.affine e out))) = true ↔
      ∀ n ∈ (Gate.base (.affine e out)).references, n < values.length := by
  change e.2.all (fun t => decide (t.2 < values.length)) = true ↔
      ∀ n ∈ e.2.map Prod.snd, n < values.length
  simp only [List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro all n mem
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp mem
    subst n
    exact all t ht
  · intro all t mem
    exact all _ (List.mem_map.mpr ⟨t,mem,rfl⟩)

private theorem parserCalibrates (values : List Nat) (g : Gate) :
    parser (values,encodeGate g) = true ↔ ∀ n ∈ g.references, n < values.length := by
  cases g with
  | base g =>
      cases g with
      | affine e out => exact allAffine values e out
      | collapse w =>
          simp [parser,encodeGate,tag,source,Gate.references,OriginalMixedGateSequential.Gate.references]
  | field g =>
      cases g with
      | iterate k s o =>
          simp [parser,encodeGate,tag,source,Gate.references,OriginalNaturalFieldGates.Gate.references,
            OriginalNaturalFieldGates.Gate.source]
      | entry P s o =>
          cases P <;> simp [parser,encodeGate,tag,source,Gate.references,
            OriginalNaturalFieldGates.Gate.references,OriginalNaturalFieldGates.Gate.source]
      | count P s o =>
          cases P <;> simp [parser,encodeGate,tag,source,Gate.references,
            OriginalNaturalFieldGates.Gate.references,OriginalNaturalFieldGates.Gate.source]

private theorem identityCalibrates (mu : NONote) (x : Nat) :
    identityGuard (rawNoteEncode mu.1,x) = true ↔ IdentityDomain mu x := by
  have norm : rawNormCode (rawNoteEncode mu.1) = actualOrdinalNorm mu.1.repr :=
    (rawNormCodeCorrect mu.1).trans (actualOrdinalNorm_notationCorrespondence mu).symm
  have shape := terminalEntryScanGuardExact.2 (rawNoteEncode mu.1,rawNoteEncode mu.1)
  change terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) = true ↔
    ONote.NF (rawNoteDecode (rawNoteEncode mu.1)) ∧ ONote.NF (rawNoteDecode (rawNoteEncode mu.1)) ∧
    ((rawNoteDecode (rawNoteEncode mu.1)).repr = 0 ∨
      Order.IsSuccLimit (rawNoteDecode (rawNoteEncode mu.1)).repr) at shape
  rw [rawNoteDecodeEncode] at shape
  unfold identityGuard
  rw [Bool.and_eq_true_iff,decide_eq_true_eq,norm]
  exact ⟨fun h => ⟨(shape.mp h.1).2.2,h.2⟩,
    fun h => ⟨shape.mpr ⟨mu.2,mu.2,h.1⟩,h.2⟩⟩

theorem exactNumericParserAndIdentity : ExactNumericParserAndIdentity :=
  ⟨parserPrimitive,identityGuardPrimitive,parserCalibrates,identityCalibrates⟩

private theorem packBaseCalibrates (r : Option Nat) : packBase r = packResult (baseResult r) := by
  cases r <;> rfl

private theorem packFieldCalibrates (r : ClosedNaturalFieldResult) :
    packField r = packResult (fieldResult r) := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

private theorem signedCalibrates (values : List Nat) (e : Expression) (out : Nat) :
    signedBank (values,encodeGate (.base (.affine e out))) =
      NaturalAffineGateGraph.signedValue e (bank values) := by
  change e.1 + e.2.foldr (fun t acc => t.1 * (bank values t.2 : Int) + acc) 0 =
    e.1 + (e.2.map (fun t => t.1 * (bank values t.2 : Int))).sum
  congr 1
  generalize e.2 = ts
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.foldr_cons,List.map_cons,List.sum_cons,ih]

private theorem packAffineCalibrates (z : Int) :
    packAffine z = packResult (baseResult (if 0 ≤ z then some z.toNat else none)) := by
  cases z with
  | ofNat n => cases n <;> simp [packAffine,Int.sign,baseResult,packResult]
  | negSucc n => simp [packAffine,Int.sign,baseResult,packResult]

private theorem identityValueCalibrates (mu : NONote) (x y : Nat) :
    identityValueCode (rawNoteEncode mu.1,x,y) = packResult (fieldResult (identityRead mu x y)) := by
  have compare := identityCalibrates mu x
  by_cases hd : IdentityDomain mu x
  · have code := compare.mpr hd
    simp [identityValueCode,code,identityRead,hd,fieldResult,packResult]
  · have code : identityGuard (rawNoteEncode mu.1,x) = false := by
      cases h : identityGuard (rawNoteEncode mu.1,x)
      · rfl
      · exact (hd (compare.mp h)).elim
    simp [identityValueCode,code,identityRead,hd,fieldResult,packResult]

private theorem coreCalibrates (f : Nat → Nat) (values : List Nat) (g : Gate) :
    readCore f (values,encodeGate g) = packResult (g.read f (bank values)) := by
  cases g with
  | base g =>
      cases g with
      | affine e out =>
          change packAffine (signedBank (values,encodeGate (.base (.affine e out)))) =
            packResult (baseResult (if 0 ≤ NaturalAffineGateGraph.signedValue e (bank values)
              then some (NaturalAffineGateGraph.signedValue e (bank values)).toNat else none))
          rw [signedCalibrates]
          exact packAffineCalibrates _
      | collapse w => exact packBaseCalibrates _
  | field g =>
      cases g with
      | iterate k s o => exact packFieldCalibrates _
      | entry P s o =>
          cases P with
          | proper lam mu => exact packFieldCalibrates _
          | identity mu => exact identityValueCalibrates mu (bank values s) (bank values s)
      | count P s o =>
          cases P with
          | proper lam mu => exact packFieldCalibrates _
          | identity mu => exact identityValueCalibrates mu (bank values s) 0

private theorem packBasePositive (p : Option Nat) : packBase p ≠ 0 := by
  cases p with
  | none => decide
  | some n => change n + 4 ≠ 0; omega

private theorem packFieldPositive (p : ClosedNaturalFieldResult) : packField p ≠ 0 := by
  cases p with
  | none => decide
  | some q =>
      cases q with
      | none => decide
      | some n => change n + 4 ≠ 0; omega

private theorem packAffinePositive (z : Int) : packAffine z ≠ 0 := by
  unfold packAffine
  split <;> omega

private theorem identityPositive (p : Nat × Nat × Nat) : identityValueCode p ≠ 0 := by
  unfold identityValueCode
  split <;> omega

private theorem corePositive (f : Nat → Nat) (p : Args) : readCore f p ≠ 0 := by
  unfold readCore
  split
  · exact packAffinePositive _
  split
  · exact packBasePositive _
  split
  · exact packFieldPositive _
  split
  · exact packFieldPositive _
  split
  · exact packFieldPositive _
  split <;> exact identityPositive _

theorem exactNumericGateRead : ExactNumericGateRead := by
  refine ⟨readComputable,?_,?_⟩
  · intro f p
    cases h : parser p <;> simp [readCode,h,corePositive]
  · intro f values g all
    have admitted := (parserCalibrates values g).mpr all
    rw [readCode,if_pos admitted]
    exact coreCalibrates f values g

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
