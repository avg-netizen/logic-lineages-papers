module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GraphInterface LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives

theorem introduction {n inputs ctx : Nat} (p : Program n) (v : List.Vector (Term ctx) inputs)
 (etag : Nat) (he : (nodes p)[etag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩)
 (a w code : Program inputs) (av wv cv : Term ctx)
 (ha : Computes p a v av) (hw : Computes p w v wv) (hc : Computes p code v cv) :
 Computes p (introduce a w code) v (introValue etag av wv cv) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p v _ etag he _ (av ::ᵥ wv ::ᵥ cv ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact ha
 | succ i => cases i using Fin.cases with
  | zero => exact hw
  | succ i => cases i using Fin.cases with
   | zero => exact hc
   | succ i => exact Fin.elim0 i

theorem graph {n ctx : Nat} (p : Program n) (v : List.Vector (Term ctx) 7) (J : Tags) (I : Installation p J)
 (ntag etag : Nat) (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩) :
 Computes p program v (value J ntag etag v) := by
 have hi := TemplateGraph.quoteGraph p v bodyTemplate innerEnvironment innerArguments (innerInputs ntag v)
  J.ctag J.atag I.hc I.ha (GraphInputs.inner p v ntag hn)
 have ho := TemplateGraph.quoteGraph p v (.ex bodyTemplate) outerEnvironment outerArguments (outerInputs ntag v)
  J.ctag J.atag I.hc I.ha (GraphInputs.outer p v ntag hn)
 have hfirst := introduction p v etag he _ _ _ _ _ _ hi (GraphInputs.quoted p v ntag hn 3) (projection p v 6)
 have hsecond := introduction p v etag he _ _ _ _ _ _ ho (GraphInputs.quoted p v ntag hn 2) hfirst
 exact CurrentExistentialIntroductionProgram.GraphOperations.liftGraph p v J I _ _ _ _ _ _
  (CurrentExistentialIntroductionProgram.GraphSyntax.unaryGraph p v J I 11 _ _ ho)
  (projection p v 5) hsecond
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphProof
