module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericLeastEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTypingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericAuxClassesProof
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowScalarAlgorithm (Settings admitted edge vertices least)
open NumberedWindowAnnotationAlgorithm (arrow annotations)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAuxExchangeLiftTypingProof (admissionAux)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (header exact_LiteralScalarEdgeHeader roundsInvariant)
open NumberedWindowInternalLiteralNumericLeastEdgeProof (exact_LiteralNumericLeastEdge)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast)
open NumberedWindowClassAlgorithm (rounds)

/-- Separately normalize the actual function and argument in the same
context and their own checked types. No literal equality of children
is asserted when the exchange can change their raw syntax. -/
def auxClasses (s : Settings) (ctx : List Nat) (q : Nat) : Option (Nat × Nat × Option Nat × Option Nat) :=
  match unpackNode q with
  | some (6,[dom,cod,fn,arg]) => some (dom,cod,least s ctx (arrow dom cod) fn,least s ctx dom arg)
  | _ => none

private theorem typedNeedsSyntax (s : Settings) (ctx : List Nat) (ty x : Nat)
    (h : admitted s ctx ty x = true) : (syntaxBits x).1 = true := by
  simp only [admitted,NumberedWindowLexicalAlgorithm.typed,Bool.and_eq_true] at h
  exact h.1.1.1

private theorem exactFields (q : Nat) (fs : List Nat)
    (valid : (syntaxBits q).1 = true) (h : unpackNode q = some (6,fs)) :
    ∃ d c f a, fs = [d,c,f,a] ∧ q = auxRaw d c f a := by
  simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,h,Option.any_some] at valid
  rcases fs with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨a,_ | ⟨x,xs⟩⟩⟩⟩⟩ <;>
    simp [NumberedWindowSyntaxAlgorithm.termParts] at valid
  exact ⟨d,c,f,a,rfl,codeOfNode h⟩

private theorem resultType (s : Settings) (ctx : List Nat) (ty d c f a : Nat)
    (h : admitted s ctx ty (auxRaw d c f a) = true) : c = ty := by
  have annotation : (annotations (auxRaw d c f a)).1 = c := by
    simp [annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,NumberedWindowAnnotationAlgorithm.termParts]
  simp only [admitted,NumberedWindowLexicalAlgorithm.typed,Bool.and_eq_true,beq_iff_eq,annotation] at h
  exact h.1.1.2

private theorem moveChild (s : Settings) (ctx : List Nat) (ty a b : Nat)
    (ha : admitted s ctx ty a = true) (hb : admitted s ctx ty b = true)
    (moved : (row s.equivalentHeads a b).1 = true) :
    edge s ctx ty a b = true := by
  have one := typedNeedsSyntax s ctx ty a ha
  have two := typedNeedsSyntax s ctx ty b hb
  simp [edge,bits,ha,hb,one,two,moved]

theorem exact_LiteralAuxClassEdge (s : Settings) (covered : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (ctx : List Nat) (ty q r : Nat)
    (held : edge s ctx ty q r = true) : auxClasses s ctx q = auxClasses s ctx r := by
  have tags := exact_LiteralScalarEdgeHeader s ctx ty q r held
  have checkedEnds : admitted s ctx ty q = true ∧ admitted s ctx ty r = true := by
    simp only [edge,Bool.and_eq_true] at held
    exact ⟨held.1.2,held.2⟩
  have qSyn := typedNeedsSyntax s ctx ty q checkedEnds.1
  have rSyn := typedNeedsSyntax s ctx ty r checkedEnds.2
  cases hq : unpackNode q with
  | none => simp [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,hq] at qSyn
  | some p =>
    obtain ⟨tag,fs⟩ := p
    cases hr : unpackNode r with
    | none => simp [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,hr] at rSyn
    | some p =>
      obtain ⟨tag',gs⟩ := p
      have equal : tag = tag' := by simpa [header,hq,hr] using tags
      subst tag'
      by_cases aux : tag = 6
      · subst tag
        obtain ⟨d,c,f,a,rfl,kq⟩ := exactFields q fs qSyn hq
        obtain ⟨d',c',g,b,rfl,kr⟩ := exactFields r gs rSyn hr
        have move : (row s.equivalentHeads (auxRaw d c f a) (auxRaw d' c' g b)).1 = true := by
          rw [← kq,← kr]
          simp only [edge,bits,Bool.and_eq_true] at held
          exact held.1.1.2
        rw [rowAuxPair] at move
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at move
        obtain ⟨⟨dd,cc⟩,one⟩ := move
        subst d'
        subst c'
        have atQ : admitted s ctx ty (auxRaw d c f a) = true := kq ▸ checkedEnds.1
        have atR : admitted s ctx ty (auxRaw d c g b) = true := kr ▸ checkedEnds.2
        obtain rfl := resultType s ctx ty d c f a atQ
        rw [admissionAux] at atQ atR
        simp only [Bool.and_eq_true] at atQ atR
        have hF : least s ctx (arrow d c) f = least s ctx (arrow d c) g := by
          rcases one with fn | arg
          · exact exact_LiteralNumericLeastEdge s covered symmetric ctx (arrow d c) f g
              (moveChild s ctx (arrow d c) f g atQ.1.2 atR.1.2 fn.1)
          · rw [arg.1]
        have hA : least s ctx d a = least s ctx d b := by
          rcases one with fn | arg
          · rw [fn.2]
          · exact exact_LiteralNumericLeastEdge s covered symmetric ctx d a b
              (moveChild s ctx d a b atQ.2 atR.2 arg.2)
        simp [auxClasses,hq,hr,hF,hA]
      · have neq : ∀ (xs : List Nat), (match some (tag,xs) with
            | some (6,[d,c,f,a]) => some (d,c,least s ctx (arrow d c) f,least s ctx d a)
            | _ => none) = (none : Option (Nat × Nat × Option Nat × Option Nat)) := by
          intro xs
          cases tag with
          | zero => rfl
          | succ tag =>
            cases tag with
            | zero => rfl
            | succ tag =>
              cases tag with
              | zero => rfl
              | succ tag =>
                cases tag with
                | zero => rfl
                | succ tag =>
                  cases tag with
                  | zero => rfl
                  | succ tag =>
                    cases tag with
                    | zero => rfl
                    | succ tag =>
                      cases tag with
                      | zero => contradiction
                      | succ tag => rfl
        unfold auxClasses
        rw [hq,hr]
        exact (neq fs).trans (neq gs).symm

theorem exact_LiteralPackedLeastAuxClasses (s : Settings) (covered : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (ctx ty q r : Nat)
    (held : packedLeast s ctx ty q = some r) :
    ∀ g, unpack ctx = some g → auxClasses s g q = auxClasses s g r := by
  intro g tag
  unfold packedLeast at held
  have one : least s g ty q = some r := by simpa [tag] using held
  let pool := vertices s q
  change (rounds (edge s g ty) pool q pool.length).min? = some r at one
  exact roundsInvariant (auxClasses s g) (exact_LiteralAuxClassEdge s covered symmetric g ty)
    pool q pool.length r (List.min?_eq_some_iff.mp one).1

#print axioms exact_LiteralAuxClassEdge
#print axioms exact_LiteralPackedLeastAuxClasses
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericAuxClassesProof
