module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SyntaxProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SeedTag
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourPlugProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowSubstitution GorbowFormulaSubstitution FixedFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

def plugged {n : Nat} (f : Formula (n+4)) (a b c d : Nat) : Formula n :=
 substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug n a)
  (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (n+1) b)
   (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (n+2) c)
    (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (n+3) d) f)))
def appended {n ctx : Nat} (raw : List.Vector (Term ctx) n) (a b c d : Term ctx) : List.Vector (Term ctx) (n+4) :=
 TagPlug.appendRaw (TagPlug.appendRaw (TagPlug.appendRaw (TagPlug.appendRaw raw a) b) c) d

theorem formula {arity n ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) n) (ca cb cc cd : Term ctx) (a b c d : Nat)
 (hca : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ca (rawNumeral (Term.numeral a))))
 (hcb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cb (rawNumeral (Term.numeral b))))
 (hcc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cc (rawNumeral (Term.numeral c))))
 (hcd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cd (rawNumeral (Term.numeral d))))
 (f : Formula (n+4)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (appended raw ca cb cc cd) f (PrescribedRuntimeSpecialization.runtimeEnvironment (n+4)))
   (formulaValue ctag atag raw (plugged f a b c d) (PrescribedRuntimeSpecialization.runtimeEnvironment n)))) := by
 obtain ⟨h1⟩ := TagRuntime.formula p ctag atag hc ha (TagPlug.appendRaw (TagPlug.appendRaw (TagPlug.appendRaw raw ca) cb) cc) cd d hcd f
 obtain ⟨h2⟩ := TagRuntime.formula p ctag atag hc ha (TagPlug.appendRaw (TagPlug.appendRaw raw ca) cb) cc c hcc _
 obtain ⟨h3⟩ := TagRuntime.formula p ctag atag hc ha (TagPlug.appendRaw raw ca) cb b hcb _
 obtain ⟨h4⟩ := TagRuntime.formula p ctag atag hc ha raw ca a hca _
 exact ⟨Logic.trans _ _ _ h1 (Logic.trans _ _ _ h2 (Logic.trans _ _ _ h3 h4))⟩

theorem head {arity n ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) n) (ca cb cc cd : Term ctx) (a b c d : Nat)
 (hca : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ca (rawNumeral (Term.numeral a))))
 (hcb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cb (rawNumeral (Term.numeral b))))
 (hcc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cc (rawNumeral (Term.numeral c))))
 (hcd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cd (rawNumeral (Term.numeral d))))
 (f : Formula (n+5)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (appended raw ca cb cc cd) f (PrescribedRuntimeSpecialization.headEnvironment (n+4)))
   (formulaValue ctag atag raw (plugged f a b c d) (PrescribedRuntimeSpecialization.headEnvironment n)))) := by
 obtain ⟨h1⟩ := TagRuntime.headFormula p ctag atag hc ha (TagPlug.appendRaw (TagPlug.appendRaw (TagPlug.appendRaw raw ca) cb) cc) cd d hcd f
 obtain ⟨h2⟩ := TagRuntime.headFormula p ctag atag hc ha (TagPlug.appendRaw (TagPlug.appendRaw raw ca) cb) cc c hcc _
 obtain ⟨h3⟩ := TagRuntime.headFormula p ctag atag hc ha (TagPlug.appendRaw raw ca) cb b hcb _
 obtain ⟨h4⟩ := TagRuntime.headFormula p ctag atag hc ha raw ca a hca _
 exact ⟨Logic.trans _ _ _ h1 (Logic.trans _ _ _ h2 (Logic.trans _ _ _ h3 h4))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourPlugProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourPlugProof
