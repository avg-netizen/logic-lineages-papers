module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem unaryAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (values : List.Vector (Term ctx) arity) (f : Program arity) (a : Term ctx)
 (hf : Computes p G f values a) :
 Computes p G (FixedFormulaSubstitution.unary tag f) values (FixedFormulaSubstitution.unaryValue ctag tag a) :=
 binary p G values HistoryCodec.cons _ _ _ _ _ (constantValue p G values tag) hf (copies p G _ ctag hc _)

theorem conclusionAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (isExists : Bool) (f g : Program arity) (values : List.Vector (Term ctx) arity) (a b : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) :
 Computes p G (conclusion isExists f g) values (conclusionValue isExists ctag atag a b) := by
 cases isExists with
 | false =>
  exact UniformClosedPropositional.ConstructorProof.binaryAt p G ctag atag hc ha values _ _ _ _
   (UniformClosedPropositional.ConstructorProof.binaryAt p G ctag atag hc ha values _ _ _ _
    (unaryAt p G ctag 6 hc values f a hf) (unaryAt p G ctag 6 hc values g b hg))
   (UniformClosedPropositional.ConstructorProof.binaryAt p G ctag atag hc ha values g f b a hg hf)
 | true =>
  exact UniformClosedPropositional.ConstructorProof.binaryAt p G ctag atag hc ha values _ _ _ _
   (unaryAt p G ctag 6 hc values _ _ (unaryAt p G ctag 10 hc values _ _ (unaryAt p G ctag 6 hc values f a hf)))
   (unaryAt p G ctag 11 hc values f a hf)

theorem argumentsAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (isExists : Bool) (f g : Program arity) (values : List.Vector (Term ctx) arity) (a b : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) :
 Computes p G (arguments isExists f g) values (argumentsValue isExists ctag a b) := by
 have hz := constantValue p G values 0
 have htail : Computes p G (if isExists then constant arity 0 else applyTwo HistoryCodec.cons g (constant arity 0))
  values (if isExists then .zero else HistoryLookup.consCall ctag b .zero) := by
  cases isExists with
  | false => exact binary p G values HistoryCodec.cons _ _ _ _ _ hg hz (copies p G _ ctag hc _)
  | true => exact hz
 exact binary p G values HistoryCodec.cons _ _ _ _ _ hf htail (copies p G _ ctag hc _)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphSupport
