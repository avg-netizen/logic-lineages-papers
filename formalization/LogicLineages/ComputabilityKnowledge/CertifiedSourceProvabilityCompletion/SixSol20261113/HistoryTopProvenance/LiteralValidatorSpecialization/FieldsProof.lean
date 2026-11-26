module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.DecoderBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.FieldsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem fieldsValid {n ctx : Nat} (p : Program n) (ltag ftag ptag leftTag rightTag : Nat)
 (hline : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (line context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (lineFields ltag leftTag rightTag line context raw)
     (.equal (LiteralSyntaxValidator.formulaCall ftag context raw) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := lineFields ltag leftTag rightTag line context raw
 let L := LiteralSyntaxValidator.lineCall ltag line
 let F := LiteralSyntaxValidator.formulaCall ftag context raw
 let Q := Formula.equal F (.succ .zero)
 let Z := Formula.equal F .zero
 obtain ⟨heq⟩ := DecoderBindingProof.lineDecoded p ltag ftag ptag leftTag rightTag hline hf hp hl hr line
 obtain ⟨hbool⟩ := LiteralSyntaxValidator.BooleanProof.internalBoolean n p ftag hf ctx context raw
 have zeroCase : Hilbert.Local T ctx [H] (.imp Z Q) := by
   have hz : Hilbert.Local T ctx [Z,H] Z := .hypothesis List.mem_cons_self
   have hh : Hilbert.Local T ctx [Z,H] H := .hypothesis (by simp)
   have hcontext := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
   have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
   have hraw := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
   have hnz := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrest
   have hc : Hilbert.Local T ctx [Z,H] (.equal
     (LiteralSyntaxValidator.formulaCall ftag (call leftTag (line ::ᵥ nil))
       (call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil))) F) :=
     HistoryIteratorSuffix.StepSuffixProof.pairCongruence ftag _ _ context raw hcontext hraw
   have hzero := localTrans _ _ _ (.base heq) (localTrans _ _ _ hc hz)
   exact Hilbert.Local.discharge (Hilbert.Local.explosion Q hzero hnz)
 have oneCase : Hilbert.Local T ctx [H] (.imp Q Q) := .base (Hilbert.identity Q)
 have result : Hilbert.Local T ctx [H] Q :=
   .mp (.mp (.mp (.base (.logical (.orElim Z Q Q))) zeroCase) oneCase) (.base hbool)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge result)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.FieldsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.FieldsProof
