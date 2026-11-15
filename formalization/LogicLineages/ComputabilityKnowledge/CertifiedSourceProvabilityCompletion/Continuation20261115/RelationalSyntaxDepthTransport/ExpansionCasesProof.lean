module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRecognitionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionIndexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel
open ConstructorStepTargets ExpansionCasesTargets ExpansionCasesSupportProof

theorem casesNonempty {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (P Q : Formula ctx)
 (hy : Nonempty (Hilbert.Local T ctx (P :: G) Q))
 (hn : Nonempty (Hilbert.Local T ctx (.neg P :: G) Q)) : Nonempty (Hilbert.Local T ctx G Q) := by
 obtain ⟨hy⟩ := hy
 obtain ⟨hn⟩ := hn
 exact ⟨ExpansionCasesSupportProof.cases P Q hy hn⟩

/-- Exhaustive internal finite case analysis on arbitrary decoded task kinds
and raw tokens, retaining the genuine positive index witness. -/
theorem expansionSuccessCases : ExpansionCasesTargets.InternalExpansionSuccessCases := by
 intro n p etag ptag ctag dtag l r he hp hc hd hl hr ctx task tok added
 let T := GorbowPRNumeralCalculation.Theory p
 let S := Formula.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added)
 let Q := casesFormula ptag ctag dtag l r task tok added
 have hout : Nonempty (Hilbert.Local T ctx [S] Q) := by
  apply casesNonempty (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)) Q
  ·
   apply casesNonempty (.equal tok (Term.numeral 0)) Q
   ·
    obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 0)), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
     task tok added (.term 0) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
    exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 0) constructors (by simp [constructors]) hcse⟩
   ·
    apply casesNonempty (.equal tok (Term.numeral 1)) Q
    ·
     obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 1)), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
      task tok added (.term 1) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
     exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 1) constructors (by simp [constructors]) hcse⟩
    ·
     apply casesNonempty (.equal tok (Term.numeral 2)) Q
     ·
      obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 2)), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
       task tok added (.term 2) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
      exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 2) constructors (by simp [constructors]) hcse⟩
     ·
      apply casesNonempty (.equal tok (Term.numeral 3)) Q
      ·
       obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 3)), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
        task tok added (.term 3) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
       exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 3) constructors (by simp [constructors]) hcse⟩
      ·
       apply casesNonempty (.equal tok (Term.numeral 4)) Q
       ·
        obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 4)), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
         task tok added (.term 4) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
        exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 4) constructors (by simp [constructors]) hcse⟩
       ·
        apply casesNonempty (.equal tok (Term.numeral 5)) Q
        ·
         obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 5)), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag ptag ctag l r he hp hc hl hr
          task tok added (.term 5) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
         exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.term 5) constructors (by simp [constructors]) hcse⟩
        ·
         have hmem : ∀ i : Fin 6, Formula.neg (.equal tok (Term.numeral i.val)) ∈ [(.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] := by
          intro i
          have hi := i.isLt
          have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by omega
          rcases hcases with h | h | h | h | h | h
          all_goals simp [h]
         have hz := ExpansionRuntimeProof.termReject p [(.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] l hl task tok (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (fun i => .hypothesis (hmem i))
         exact ExpansionIndexProof.rejectSuccess p [(.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)), S] etag he task tok added Q (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) hz
  ·
   apply casesNonempty (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)) Q
   ·
    apply casesNonempty (.equal tok (Term.numeral 0)) Q
    ·
     obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 0)), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
      task tok added (.formula 0) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
     exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 0) constructors (by simp [constructors]) hcse⟩
    ·
     apply casesNonempty (.equal tok (Term.numeral 1)) Q
     ·
      obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 1)), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
       task tok added (.formula 1) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
      exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 1) constructors (by simp [constructors]) hcse⟩
     ·
      apply casesNonempty (.equal tok (Term.numeral 2)) Q
      ·
       obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 2)), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
        task tok added (.formula 2) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
       exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 2) constructors (by simp [constructors]) hcse⟩
      ·
       apply casesNonempty (.equal tok (Term.numeral 3)) Q
       ·
        obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 3)), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
         task tok added (.formula 3) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
        exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 3) constructors (by simp [constructors]) hcse⟩
       ·
        apply casesNonempty (.equal tok (Term.numeral 4)) Q
        ·
         obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 4)), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
          task tok added (.formula 4) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
         exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 4) constructors (by simp [constructors]) hcse⟩
        ·
         apply casesNonempty (.equal tok (Term.numeral 5)) Q
         ·
          obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 5)), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
           task tok added (.formula 5) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
          exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 5) constructors (by simp [constructors]) hcse⟩
         ·
          apply casesNonempty (.equal tok (Term.numeral 6)) Q
          ·
           obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 6)), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
            task tok added (.formula 6) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
           exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 6) constructors (by simp [constructors]) hcse⟩
          ·
           apply casesNonempty (.equal tok (Term.numeral 7)) Q
           ·
            obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 7)), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
             task tok added (.formula 7) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
            exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 7) constructors (by simp [constructors]) hcse⟩
           ·
            apply casesNonempty (.equal tok (Term.numeral 8)) Q
            ·
             obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 8)), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
              task tok added (.formula 8) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
             exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 8) constructors (by simp [constructors]) hcse⟩
            ·
             apply casesNonempty (.equal tok (Term.numeral 9)) Q
             ·
              obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 9)), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
               task tok added (.formula 9) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
              exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 9) constructors (by simp [constructors]) hcse⟩
             ·
              apply casesNonempty (.equal tok (Term.numeral 10)) Q
              ·
               obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 10)), (.neg (.equal tok (Term.numeral 9))), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
                task tok added (.formula 10) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
               exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 10) constructors (by simp [constructors]) hcse⟩
              ·
               apply casesNonempty (.equal tok (Term.numeral 11)) Q
               ·
                obtain ⟨hcse⟩ := ExpansionRecognitionProof.constructorCaseAt p [(.equal tok (Term.numeral 11)), (.neg (.equal tok (Term.numeral 10))), (.neg (.equal tok (Term.numeral 9))), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag ptag ctag l r he hp hc hl hr
                 task tok added (.formula 11) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
                exact ⟨ExpansionRecognitionProof.injectConstructor ptag ctag dtag l r task tok added (.formula 11) constructors (by simp [constructors]) hcse⟩
               ·
                have hmem : ∀ i : Fin 12, Formula.neg (.equal tok (Term.numeral i.val)) ∈ [(.neg (.equal tok (Term.numeral 11))), (.neg (.equal tok (Term.numeral 10))), (.neg (.equal tok (Term.numeral 9))), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] := by
                 intro i
                 have hi := i.isLt
                 have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
                 rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
                 all_goals simp [h]
                have hz := ExpansionRuntimeProof.formulaReject p [(.neg (.equal tok (Term.numeral 11))), (.neg (.equal tok (Term.numeral 10))), (.neg (.equal tok (Term.numeral 9))), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] l hl task tok (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (fun i => .hypothesis (hmem i))
                exact ExpansionIndexProof.rejectSuccess p [(.neg (.equal tok (Term.numeral 11))), (.neg (.equal tok (Term.numeral 10))), (.neg (.equal tok (Term.numeral 9))), (.neg (.equal tok (Term.numeral 8))), (.neg (.equal tok (Term.numeral 7))), (.neg (.equal tok (Term.numeral 6))), (.neg (.equal tok (Term.numeral 5))), (.neg (.equal tok (Term.numeral 4))), (.neg (.equal tok (Term.numeral 3))), (.neg (.equal tok (Term.numeral 2))), (.neg (.equal tok (Term.numeral 1))), (.neg (.equal tok (Term.numeral 0))), (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag he task tok added Q (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) hz
   ·
    apply casesNonempty (.equal (call l (task ::ᵥ nil)) (Term.numeral 2)) Q
    ·
     obtain ⟨hi⟩ := ExpansionIndexProof.indexCaseAt p [(.equal (call l (task ::ᵥ nil)) (Term.numeral 2)), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 1))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag l r dtag he hl hr hd task tok added
      (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token]))
     exact ⟨ExpansionRecognitionProof.injectIndex ptag ctag dtag l r task tok added constructors hi⟩
    ·
     have hmem : ∀ i : Fin 3, Formula.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral i.val)) ∈ [(.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 1))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] := by
      intro i
      have hi := i.isLt
      have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hcases with h | h | h
      all_goals simp [h]
     have hz := ExpansionRuntimeProof.kindReject p [(.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 1))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] l hl task tok (fun i => .hypothesis (hmem i))
     exact ExpansionIndexProof.rejectSuccess p [(.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 1))), (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral 0))), S] etag he task tok added Q (.hypothesis (by simp [S, ConstructorStepTargets.kind, ConstructorStepTargets.token])) hz
 obtain ⟨hout⟩ := hout
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesProof
