module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootLeavesPrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedAuxiliaryDecoding NumberedDirectCertificate NumberedSelectCertificate
open NumberedCopyCertificate NumberedUniformPackedDecoding NumberedUniformSelector
open NumberedDirectOperations NumberedAuxiliarySubstitution NumberedSelfApplication NumberedCopyOperation

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem outputCodeCalibration {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (tau : Ty) (output : Option (Packed (Fin n) arity Gamma))
    (target : Packed (Fin n) arity Gamma)
    (htype : ∀ q, output = some q → q.1 = tau) :
    outputCodeTest tau (output.map (fun q => termCode q.2)) (packedCode target) =
      decide (output = some target) := by
  cases output with
  | none => simp [outputCodeTest]
  | some q =>
    have hpair : (tau,termCode q.2) = packedCode q :=
      congrArg (fun t : Ty => (t,termCode q.2)) (htype q rfl).symm
    simp only [Option.map_some,outputCodeTest,hpair,Option.some.injEq,
      (NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity Gamma).eq_iff]

theorem putCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (label : Nat) (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (putCode label q.1 (termCode q.2)) (packedCode r) =
      decide (directTarget arity Gamma (.put label) q = some r) := by
  rw [NumberedDirectOperationsSupportProof.putCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedDirectOperationsSupportProof.directTypePreservation n arity Gamma (.put label) q s hs)

theorem abstractionCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (abstractionCode (termCode q.2)) (packedCode r) =
      decide (directTarget arity Gamma .abstraction q = some r) := by
  rw [NumberedDirectOperationsSupportProof.abstractionCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedDirectOperationsSupportProof.directTypePreservation n arity Gamma .abstraction q s hs)

theorem betaCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (betaCode Gamma.length (termCode q.2)) (packedCode r) =
      decide (directTarget arity Gamma .beta q = some r) := by
  rw [NumberedAuxiliaryBetaSupportProof.betaCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedDirectOperationsSupportProof.directTypePreservation n arity Gamma .beta q s hs)

theorem bottomCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (bottomCode q.1 (termCode q.2)) (packedCode r) =
      decide (directTarget arity Gamma .bottom q = some r) := by
  rw [NumberedDirectOperationsSupportProof.bottomCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedDirectOperationsSupportProof.directTypePreservation n arity Gamma .bottom q s hs)

theorem selectCalibration (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (index : Nat) (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (selectCode types index q.1 (termCode q.2)) (packedCode r) =
      decide (selectTarget arity Gamma types index q = some r) := by
  rw [NumberedSelfApplicationSupportProof.selectCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedSelfApplicationProof.selectTypePreservation n arity Gamma types index q s hs)

theorem copyCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (head : HeadCode (Fin n))
    (q r : Packed (Fin n) arity Gamma) :
    outputCodeTest q.1 (copyCode arity symbols S table head (termCode q.2)) (packedCode r) =
      decide (copyTarget arity symbols S table Gamma (decodeHead head) q = some r) := by
  rw [NumberedCopyOperationProof.copyCodeCalibration]
  exact outputCodeCalibration q.1 _ r (fun s hs =>
    NumberedCopyOperationProof.copyTypePreservation symbols S table (decodeHead head) q s hs)

attribute [local irreducible] Primrec

theorem outputCodePrimitive (n : Nat) :
    Primrec (fun p : Ty × Option (Code (Fin n)) × RawPacked n =>
      outputCodeTest p.1 p.2.1 p.2.2) := by
  let A := Ty × Option (Code (Fin n)) × RawPacked n
  have hbody : Primrec (fun p : A × Code (Fin n) => (p.1.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hmap : Primrec (fun p : A => p.2.1.map (fun code => (p.1,code))) :=
    Primrec.option_map (Primrec.fst.comp Primrec.snd) hbody.to₂
  exact (Primrec.eq.comp hmap
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))).decide

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorSupportProof
