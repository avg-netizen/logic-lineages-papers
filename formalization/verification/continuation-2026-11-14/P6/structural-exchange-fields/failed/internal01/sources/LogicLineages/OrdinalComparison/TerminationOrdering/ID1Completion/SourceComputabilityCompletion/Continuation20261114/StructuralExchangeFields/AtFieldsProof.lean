module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TransparentHeadBranches.Proof (identityImp andImp orImp applyImp)
open SupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem eqImp (x y u v : OTerm alpha)
    (hx : Nonempty (Derivation body Delta (eqn x u)))
    (hy : Nonempty (Derivation body Delta (eqn y v))) :
    Nonempty (Derivation body Delta ((eqn x y).imp (eqn u v))) := by
  obtain ⟨hx⟩ := withHyp hx (eqn x y)
  obtain ⟨hy⟩ := withHyp hy (eqn x y)
  have hxy : Derivation body (eqn x y :: Delta) (eqn x y) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (trans (symm hx) (trans hxy hy))⟩

theorem eqReverse {x y : OTerm alpha} (h : Nonempty (Derivation body Delta (eqn x y))) :
    Nonempty (Derivation body Delta (eqn y x)) := by
  obtain ⟨h⟩ := h
  exact ⟨symm h⟩

theorem atFields : ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3) (cons : Bool)
    (node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    source sigma q a)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    target tau r b)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  ∀ (ys : Fin 19 → OTerm alpha),
  (∀ i, Nonempty (Derivation body Delta (graph3 (active U V i) (ys i) node code param))) →
  (Nonempty (Derivation body Delta (graph3 (layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓
     ((eqn a b ⊓ eqn h0 (numeral 1)) ⊔ (eqn q r ⊓ eqn h3 (numeral 1)))))) := by
  intro body alpha Delta U V cons node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3
    hV hn hsource htarget hc0 hc1 hc2 hc3 ys hy
  obtain ⟨hqs,hqt⟩ := rawSides node code param source target hn
  obtain ⟨hs0,hs1,hs5,hs6⟩ := sideGraphs U V false cons node code param source sigma q a hV hqs hsource
  obtain ⟨ht7,ht8,ht12,ht13⟩ := sideGraphs U V true cons node code param target tau r b hV hqt htarget
  have he0 := valueUnique (active U V 0) (ys 0) (numeral (if cons then 7 else 2)) ![node,code,param] (hy 0) hs0
  have he7 := valueUnique (active U V 7) (ys 7) (numeral (if cons then 7 else 2)) ![node,code,param] (hy 7) ht7
  have he1 := valueUnique (active U V 1) (ys 1) sigma ![node,code,param] (hy 1) hs1
  have he8 := valueUnique (active U V 8) (ys 8) tau ![node,code,param] (hy 8) ht8
  have he5 := valueUnique (active U V 5) (ys 5) q ![node,code,param] (hy 5) hs5
  have he6 := valueUnique (active U V 6) (ys 6) a ![node,code,param] (hy 6) hs6
  have he12 := valueUnique (active U V 12) (ys 12) r ![node,code,param] (hy 12) ht12
  have he13 := valueUnique (active U V 13) (ys 13) b ![node,code,param] (hy 13) ht13
  have htag : (if cons then 7 else 2) = 2 ∨ (if cons then 7 else 2) = 7 := by cases cons <;> simp
  have hbranch := TransparentApplicationLayer.Proof.internalApplication body alpha Delta (fields U V) V
    node code param h0 t0 h1 t1 h2 t2 h3 t3 ys (if cons then 7 else 2)
    htag hV hy he0 he7 hc0 hc1 hc2 hc3
  constructor
  · intro h
    exact applyImp (andImp (eqImp _ _ _ _ he1 he8)
      (orImp (andImp (eqImp _ _ _ _ he6 he13) (identityImp _))
        (andImp (eqImp _ _ _ _ he5 he12) (identityImp _)))) (hbranch.mp h)
  · intro h
    exact hbranch.mpr (applyImp (andImp (eqImp _ _ _ _ (eqReverse he1) (eqReverse he8))
      (orImp (andImp (eqImp _ _ _ _ (eqReverse he6) (eqReverse he13)) (identityImp _))
        (andImp (eqImp _ _ _ _ (eqReverse he5) (eqReverse he12)) (identityImp _)))) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
