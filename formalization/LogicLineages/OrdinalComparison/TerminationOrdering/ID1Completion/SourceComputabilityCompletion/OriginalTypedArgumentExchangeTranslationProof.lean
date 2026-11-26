module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTranslationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedArgumentExchange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] OriginalTypedArgumentObservations.argumentObservations OriginalTypedArgumentPrefixBuilder.mapped

theorem translationCases (R : Program 2)
 (certificate parameter numericCertificate front payload first rest second rawTail typFirst childFirst typSecond childSecond : OTerm alpha)
 (psi : Formula alpha)
 (hCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate front payload)))
 (hPayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload first rest)))
 (hRest : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rest second rawTail)))
 (hFirstPacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first typFirst childFirst)))
 (hSecondPacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing second typSecond childSecond)))
 (hTranslate : Nonempty (Derivation body Delta (graph2 (translate R) numericCertificate certificate parameter)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (w : Fin 8 → OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentPrefixBuilder.mapped R) (w 0) (front.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 R (w 1) (first.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 R (w 2) (second.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (w 3) (typFirst.relabel j) (w 1))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (w 4) (typSecond.relabel j) (w 2))) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) (w 5) (rawTail.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (w 6) (w 4) (w 5))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (w 7) (w 3) (w 6))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (numericCertificate.relabel j) (w 0) (w 7))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qFirst : Program 2 := .composition R ![firstOf (.projection 0),.projection 1]
 let qSecond : Program 2 := .composition R ![secondOf (.projection 0),.projection 1]
 let qs : Fin 8 → Program 2 := ![translatedFront R,qFirst,qSecond,translatedFirst R,translatedSecond R,translatedTail R,translatedRest R,translatedPayload R]
 let xs : Fin 2 → OTerm alpha := Fin.cons certificate (Fin.cons parameter Fin.elim0)
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j w Theta hj hq
 have hv : (fun i : Fin 2 => (xs i).relabel j) = Fin.cons (certificate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 let ys : Fin 2 → OTerm beta := Fin.cons (certificate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hq' (i : Fin 8) : Nonempty (Derivation body Theta (programGraph (qs i) (w i) ys)) := by
   simpa only [hv,ys] using hq i
 have hCertificate' := renameInto hCertificate j Theta hj
 rw [graph2Rename] at hCertificate'
 have hPayload' := renameInto hPayload j Theta hj
 rw [graph2Rename] at hPayload'
 have hRest' := renameInto hRest j Theta hj
 rw [graph2Rename] at hRest'
 have hFirstPacked' := renameInto hFirstPacked j Theta hj
 rw [graph2Rename] at hFirstPacked'
 have hSecondPacked' := renameInto hSecondPacked j Theta hj
 rw [graph2Rename] at hSecondPacked'
 have hTranslate' := renameInto hTranslate j Theta hj
 rw [graph2Rename] at hTranslate'
 have hcert : Nonempty (Derivation body Theta (programGraph (.projection 0) (certificate.relabel j) ys)) := projectionValue 0 ys
 have hparam : Nonempty (Derivation body Theta (programGraph (.projection 1) (parameter.relabel j) ys)) := projectionValue 1 ys
 have hf : Nonempty (Derivation body Theta (programGraph (frontOf (.projection 0)) (front.relabel j) ys)) :=
   unaryValue InternalUnpair.left (.projection 0) (front.relabel j) (certificate.relabel j) ys (pairLeft _ _ _ hCertificate') hcert
 have hp : Nonempty (Derivation body Theta (programGraph (payloadOf (.projection 0)) (payload.relabel j) ys)) :=
   unaryValue InternalUnpair.right (.projection 0) (payload.relabel j) (certificate.relabel j) ys (pairRight _ _ _ hCertificate') hcert
 have hfirst : Nonempty (Derivation body Theta (programGraph (firstOf (.projection 0)) (first.relabel j) ys)) :=
   unaryValue InternalUnpair.left (payloadOf (.projection 0)) (first.relabel j) (payload.relabel j) ys (pairLeft _ _ _ hPayload') hp
 have hr : Nonempty (Derivation body Theta (programGraph (restOf (.projection 0)) (rest.relabel j) ys)) :=
   unaryValue InternalUnpair.right (payloadOf (.projection 0)) (rest.relabel j) (payload.relabel j) ys (pairRight _ _ _ hPayload') hp
 have hsecond : Nonempty (Derivation body Theta (programGraph (secondOf (.projection 0)) (second.relabel j) ys)) :=
   unaryValue InternalUnpair.left (restOf (.projection 0)) (second.relabel j) (rest.relabel j) ys (pairLeft _ _ _ hRest') hr
 have htail : Nonempty (Derivation body Theta (programGraph (tailOf (.projection 0)) (rawTail.relabel j) ys)) :=
   unaryValue InternalUnpair.right (restOf (.projection 0)) (rawTail.relabel j) (rest.relabel j) ys (pairRight _ _ _ hRest') hr
 have h0 : Nonempty (Derivation body Theta (programGraph (translatedFront R) (w 0) ys)) := by
   have hselect : qs (0 : Fin 8) = translatedFront R := rfl
   simpa only [hselect] using hq' 0
 have h1 : Nonempty (Derivation body Theta (programGraph (qFirst) (w 1) ys)) := by
   have hselect : qs (1 : Fin 8) = qFirst := rfl
   simpa only [hselect] using hq' 1
 have h2 : Nonempty (Derivation body Theta (programGraph (qSecond) (w 2) ys)) := by
   have hselect : qs (2 : Fin 8) = qSecond := rfl
   simpa only [hselect] using hq' 2
 have h3 : Nonempty (Derivation body Theta (programGraph (translatedFirst R) (w 3) ys)) := by
   have hselect : qs (3 : Fin 8) = translatedFirst R := rfl
   simpa only [hselect] using hq' 3
 have h4 : Nonempty (Derivation body Theta (programGraph (translatedSecond R) (w 4) ys)) := by
   have hselect : qs (4 : Fin 8) = translatedSecond R := rfl
   simpa only [hselect] using hq' 4
 have h5 : Nonempty (Derivation body Theta (programGraph (translatedTail R) (w 5) ys)) := by
   have hselect : qs (5 : Fin 8) = translatedTail R := rfl
   simpa only [hselect] using hq' 5
 have h6 : Nonempty (Derivation body Theta (programGraph (translatedRest R) (w 6) ys)) := by
   have hselect : qs (6 : Fin 8) = translatedRest R := rfl
   simpa only [hselect] using hq' 6
 have h7 : Nonempty (Derivation body Theta (programGraph (translatedPayload R) (w 7) ys)) := by
   have hselect : qs (7 : Fin 8) = translatedPayload R := rfl
   simpa only [hselect] using hq' 7
 have hmapped := binaryRecover (OriginalTypedArgumentPrefixBuilder.mapped R) (frontOf (.projection 0)) (.projection 1)
   (w 0) (front.relabel j) (parameter.relabel j) ys h0 hf hparam
 have hRfirst := binaryRecover R (firstOf (.projection 0)) (.projection 1) (w 1) (first.relabel j) (parameter.relabel j) ys h1 hfirst hparam
 have hRsecond := binaryRecover R (secondOf (.projection 0)) (.projection 1) (w 2) (second.relabel j) (parameter.relabel j) ys h2 hsecond hparam
 have hcellFirst := binaryRecover (OriginalTypedArgumentPrefixBuilder.cell R) (firstOf (.projection 0)) (.projection 1)
   (w 3) (first.relabel j) (parameter.relabel j) ys h3 hfirst hparam
 have hcellSecond := binaryRecover (OriginalTypedArgumentPrefixBuilder.cell R) (secondOf (.projection 0)) (.projection 1)
   (w 4) (second.relabel j) (parameter.relabel j) ys h4 hsecond hparam
 have htailObs := binaryRecover (OriginalTypedArgumentObservations.argumentObservations R) (tailOf (.projection 0)) (.projection 1)
   (w 5) (rawTail.relabel j) (parameter.relabel j) ys h5 htail hparam
 have hnumericRest := binaryRecover InternalPairing.pairing (translatedSecond R) (translatedTail R) (w 6) (w 4) (w 5) ys h6 h4 h5
 have hnumericPayload := binaryRecover InternalPairing.pairing (translatedFirst R) (translatedRest R) (w 7) (w 3) (w 6) ys h7 h3 h6
 have hnumericCert := binaryRecover InternalPairing.pairing (translatedFront R) (translatedPayload R)
   (numericCertificate.relabel j) (w 0) (w 7) ys hTranslate' h0 h7
 let fs : Fin 2 → OTerm beta := Fin.cons (first.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 let ss : Fin 2 → OTerm beta := Fin.cons (second.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hft := unaryValue InternalUnpair.left (.projection 0) (typFirst.relabel j) (first.relabel j) fs
   (pairLeft _ _ _ hFirstPacked') (projectionValue 0 fs)
 have hst := unaryValue InternalUnpair.left (.projection 0) (typSecond.relabel j) (second.relabel j) ss
   (pairLeft _ _ _ hSecondPacked') (projectionValue 0 ss)
 have hfv := binaryValue R (.projection 0) (.projection 1) (w 1) (first.relabel j) (parameter.relabel j) fs hRfirst (projectionValue 0 fs) (projectionValue 1 fs)
 have hsv := binaryValue R (.projection 0) (.projection 1) (w 2) (second.relabel j) (parameter.relabel j) ss hRsecond (projectionValue 0 ss) (projectionValue 1 ss)
 have htypedFirst := binaryRecover InternalPairing.pairing (leftOf (.projection 0)) (.composition R ![.projection 0,.projection 1])
   (w 3) (typFirst.relabel j) (w 1) fs hcellFirst hft hfv
 have htypedSecond := binaryRecover InternalPairing.pairing (leftOf (.projection 0)) (.composition R ![.projection 0,.projection 1])
   (w 4) (typSecond.relabel j) (w 2) ss hcellSecond hst hsv
 exact next beta j Theta w hj hmapped hRfirst hRsecond htypedFirst htypedSecond htailObs hnumericRest hnumericPayload hnumericCert
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTranslationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTranslationProof
