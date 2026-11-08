module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem unaryValue {n : Nat} (p : Program 1) (q : Program n) (out x : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 p out x)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs))) :
    Nonempty (Derivation body Gamma (programGraph (.composition p (fun _ : Fin 1 => q)) out xs)) := by
  apply compositionValue p (fun _ : Fin 1 => q) out xs (Fin.cons x Fin.elim0) hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact hq

theorem unaryRecover {n : Nat} (p : Program 1) (q : Program n) (out x : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => q)) out xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs))) :
    Nonempty (Derivation body Gamma (graph1 p out x)) := by
  apply compositionRecover p (fun _ : Fin 1 => q) out xs (Fin.cons x Fin.elim0) hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact hq

theorem binaryValue {n : Nat} (p : Program 2) (q r : Program n) (out x y : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 p out x y)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs)))
    (hr : Nonempty (Derivation body Gamma (programGraph r y xs))) :
    Nonempty (Derivation body Gamma (programGraph (.composition p ![q,r]) out xs)) := by
  apply compositionValue p ![q,r] out xs (Fin.cons x (Fin.cons y Fin.elim0)) hp
  intro i
  exact Fin.cases hq (Fin.cases hr (fun k => Fin.elim0 k)) i

theorem binaryRecover {n : Nat} (p : Program 2) (q r : Program n) (out x y : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph (.composition p ![q,r]) out xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs)))
    (hr : Nonempty (Derivation body Gamma (programGraph r y xs))) :
    Nonempty (Derivation body Gamma (graph2 p out x y)) := by
  apply compositionRecover p ![q,r] out xs (Fin.cons x (Fin.cons y Fin.elim0)) hp
  intro i
  exact Fin.cases hq (Fin.cases hr (fun k => Fin.elim0 k)) i

theorem twoValue {n : Nat} (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (two n) positionTerm xs)) := by
  rw [positionTermEq]
  exact unaryValue .succ (InternalLessThan.constantOne n) (suc (suc z)) (suc z) xs
    (successorValue (Fin.cons (suc z) Fin.elim0))
    (InternalLessThanSupportProof.oneConstantValue xs)

theorem pairLeft (p x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing p x y))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left x p)) := by
  obtain ⟨d⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse body α p x y) h
  exact ⟨Derivation.conjunctionLeft d⟩

theorem pairRight (p x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing p x y))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right y p)) := by
  obtain ⟨d⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse body α p x y) h
  exact ⟨Derivation.conjunctionRight d⟩

theorem reconstructPair (p x y : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left x p)))
    (hy : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right y p))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing p x y)) := by
  obtain ⟨hx⟩ := hx
  obtain ⟨hy⟩ := hy
  exact closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body α p x y)
    ⟨Derivation.conjunctionIntroduction hx hy⟩

theorem edgeTailValue (s t k tail : OTerm α)
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tail t k))) :
    Nonempty (Derivation body Gamma (graph3 (pairOf (.projection 1) (.projection 2)) tail s t k)) :=
  binaryValue InternalPairing.pairing (.projection 1) (.projection 2) tail t k
    (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) ht
    (projectionValue 1 (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))))
    (projectionValue 2 (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))))

theorem edgeAtTail (certificate s t k tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate s tail)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tail t k))) :
    Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k)) :=
  binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 1) (.projection 2))
    certificate s tail (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hc
    (projectionValue 0 (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))))
    (edgeTailValue s t k tail ht)

theorem edgeRecoverAtTail (certificate s t k tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tail t k))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate s tail)) :=
  binaryRecover InternalPairing.pairing (.projection 0) (pairOf (.projection 1) (.projection 2))
    certificate s tail (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hc
    (projectionValue 0 (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))))
    (edgeTailValue s t k tail ht)

theorem edgeSelectorsAtTail (certificate s t k tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing tail t k))) :
    Nonempty (Derivation body Gamma (selectors certificate s t k)) := by
  have hp := edgeRecoverAtTail certificate s t k tail hc ht
  obtain ⟨hs⟩ := pairLeft certificate s tail hp
  have htail := pairRight certificate s tail hp
  obtain ⟨htt⟩ := unaryValue InternalUnpair.left InternalUnpair.right t tail
    (Fin.cons certificate Fin.elim0) (pairLeft tail t k ht) htail
  obtain ⟨hkk⟩ := unaryValue InternalUnpair.right InternalUnpair.right k tail
    (Fin.cons certificate Fin.elim0) (pairRight tail t k ht) htail
  exact ⟨Derivation.conjunctionIntroduction hs (Derivation.conjunctionIntroduction htt hkk)⟩

/-- The inner pair witness comes from existing internal totality and is
discharged by original existential elimination. -/
theorem edgeSelectors (certificate s t k : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k))) :
    Nonempty (Derivation body Gamma (selectors certificate s t k)) := by
  apply programCases InternalPairing.pairing (Fin.cons t (Fin.cons k Fin.elim0)) _
  intro β j Delta tail hj ht
  rw [selectorsRename]
  simp only [consTermRename,emptyRename] at ht
  have hc' := renameInto hc j Delta hj
  rw [graph3Rename] at hc'
  exact edgeSelectorsAtTail (certificate.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) tail hc' ht

theorem edgeReconstruction (certificate s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors certificate s t k))) :
    Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k)) := by
  apply programCases InternalUnpair.right (Fin.cons certificate Fin.elim0) _
  intro β j Delta tail hj htail
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at htail
  have h' := renameInto h j Delta hj
  rw [selectorsRename] at h'
  obtain ⟨h'⟩ := h'
  have hl : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left (t.relabel j) tail)) :=
    unaryRecover InternalUnpair.left InternalUnpair.right (t.relabel j) tail
      (Fin.cons (certificate.relabel j) Fin.elim0)
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h')⟩ htail
  have hr : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (k.relabel j) tail)) :=
    unaryRecover InternalUnpair.right InternalUnpair.right (k.relabel j) tail
      (Fin.cons (certificate.relabel j) Fin.elim0)
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h')⟩ htail
  exact edgeAtTail (certificate.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) tail
    (reconstructPair (certificate.relabel j) (s.relabel j) tail
      ⟨Derivation.conjunctionLeft h'⟩ htail)
    (reconstructPair tail (t.relabel j) (k.relabel j) hl hr)

theorem applicationComponents (d e f a fp ap : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a))) :
    ∀ i : Fin 4, Nonempty (Derivation body Gamma
      (programGraph ((![Program.projection 0,.projection 1,rightOf (.projection 2),
        rightOf (.projection 3)] : Fin 4 → Program 4) i)
        (![d,e,fp,ap] i)
        (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))))) := by
  intro i
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (unaryValue InternalUnpair.right (.projection 2) fp f xs hf (projectionValue 2 xs))
      (Fin.cases (unaryValue InternalUnpair.right (.projection 3) ap a xs ha (projectionValue 3 xs))
        (fun q => Fin.elim0 q)))) i

theorem applicationForward (d e f a fp ap out : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (h : Nonempty (Derivation body Gamma (graph4 application out d e f a))) :
    Nonempty (Derivation body Gamma (graph4 packedApplication out d e fp ap)) :=
  compositionRecover packedApplication
    ![.projection 0,.projection 1,rightOf (.projection 2),rightOf (.projection 3)] out
    (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0))))
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) h
    (applicationComponents d e f a fp ap hf ha)

theorem applicationBackward (d e f a fp ap out : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (h : Nonempty (Derivation body Gamma (graph4 packedApplication out d e fp ap))) :
    Nonempty (Derivation body Gamma (graph4 application out d e f a)) :=
  compositionValue packedApplication
    ![.projection 0,.projection 1,rightOf (.projection 2),rightOf (.projection 3)] out
    (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0))))
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) h
    (applicationComponents d e f a fp ap hf ha)

theorem prefixValue (certificate path prefixed : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left path certificate)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode prefixed positionTerm path))) :
    Nonempty (Derivation body Gamma (graph1 prefixedPath prefixed certificate)) :=
  binaryValue InternalListCodec.consCode (two 1) InternalUnpair.left prefixed positionTerm path
    (Fin.cons certificate Fin.elim0) hp (twoValue (Fin.cons certificate Fin.elim0)) hl

theorem stepForward (certificate path payload prefixed out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate path payload)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode prefixed positionTerm path)))
    (h : Nonempty (Derivation body Gamma (graph1 stepLift out certificate))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out prefixed payload)) :=
  binaryRecover InternalPairing.pairing prefixedPath InternalUnpair.right out prefixed payload
    (Fin.cons certificate Fin.elim0) h
    (prefixValue certificate path prefixed (pairLeft certificate path payload hc) hp)
    (pairRight certificate path payload hc)

theorem stepBackward (certificate path payload prefixed out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate path payload)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode prefixed positionTerm path)))
    (h : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out prefixed payload))) :
    Nonempty (Derivation body Gamma (graph1 stepLift out certificate)) :=
  binaryValue InternalPairing.pairing prefixedPath InternalUnpair.right out prefixed payload
    (Fin.cons certificate Fin.elim0) h
    (prefixValue certificate path prefixed (pairLeft certificate path payload hc) hp)
    (pairRight certificate path payload hc)

theorem stepPayloadPreserved (certificate path payload out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate path payload)))
    (hs : Nonempty (Derivation body Gamma (graph1 stepLift out certificate))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload out)) := by
  apply programCases InternalListCodec.consCode (Fin.cons positionTerm (Fin.cons path Fin.elim0)) _
  intro β j Delta prefixed hj hp
  rw [graph1Rename]
  simp only [consTermRename,emptyRename,positionTermRename] at hp
  have hc' := renameInto hc j Delta hj
  rw [graph2Rename] at hc'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  exact pairRight (out.relabel j) prefixed (payload.relabel j)
    (stepForward (certificate.relabel j) (path.relabel j) (payload.relabel j) prefixed
      (out.relabel j) hc' hp hs')

theorem stepDestruction (certificate path payload out prefixed : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing certificate path payload)))
    (hs : Nonempty (Derivation body Gamma (graph1 stepLift out certificate)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left prefixed out))) :
    Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode prefixed positionTerm path ⊓
        graph1 InternalUnpair.right payload out)) := by
  apply programCases InternalListCodec.consCode (Fin.cons positionTerm (Fin.cons path Fin.elim0)) _
  intro β j Delta prefValue hj hp
  change Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode prefixed positionTerm path).relabel j ⊓
      (graph1 InternalUnpair.right payload out).relabel j))
  rw [graph2Rename,graph1Rename,positionTermRename]
  simp only [consTermRename,emptyRename,positionTermRename] at hp
  have hc' := renameInto hc j Delta hj
  rw [graph2Rename] at hc'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hl' := renameInto hl j Delta hj
  rw [graph1Rename] at hl'
  have he := stepForward (certificate.relabel j) (path.relabel j) (payload.relabel j)
    prefValue (out.relabel j) hc' hp hs'
  have hsame := valueUnique InternalUnpair.left prefValue (prefixed.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) (pairLeft (out.relabel j) prefValue (payload.relabel j) he) hl'
  obtain ⟨hcons⟩ := outputTransport InternalListCodec.consCode prefValue (prefixed.relabel j)
    (Fin.cons positionTerm (Fin.cons (path.relabel j) Fin.elim0)) hsame hp
  obtain ⟨hpayload⟩ := pairRight (out.relabel j) prefValue (payload.relabel j) he
  exact ⟨Derivation.conjunctionIntroduction hcons hpayload⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
