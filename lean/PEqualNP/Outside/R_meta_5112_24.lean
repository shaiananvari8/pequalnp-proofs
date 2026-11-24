import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.GetD

-- The twelve positive rows and the twelve maximal negative rows suffice.
-- Repeated rows and rows contained in a maximal negative row impose no further constraint.
-- For the coverage hypothesis, a checked choice of compact row in original row order is
-- 12, 12, 12, 13, 0, 1, 15, 4, 5, 14, 2, 3, 17, 8, 9
-- 10, 18, 11, 16, 6, 7, 12, 12, 13, 13, 15, 15, 20, 14, 14
-- 23, 19, 17, 17, 21, 19, 19, 19, 18, 18, 20, 20, 20, 22, 23
-- 23, 16, 16, 21, 23, 22, 23, 21, 21, 22, 22, 23, 23
-- At positions 58 and above all original columns have zero bits, so row 12 suffices.
theorem PEqualNP.Outside.R_meta_5112_24
    (cover : let big : List ℕ := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
     let small : List ℕ := [709697, 1356164, 2308120, 4543010, 11542531, 9994288, 13123596, 11141888, 13896704, 14745792, 16277519, 16351472, 16649984]
     ∀ r : ℕ, ∃ k : Fin 24,
       (1764784 : ℕ).testBit r = (4095 : ℕ).testBit k ∧
       ∀ i : Fin 13, if (1764784 : ℕ).testBit r then
         (small.getD i 0).testBit k = true → (big.getD i 0).testBit r = true
       else
         (big.getD i 0).testBit r = true → (small.getD i 0).testBit k = true)
    (circuit : ∃ gs : List (Bool × ℕ × ℕ), 1 ≤ gs.length ∧ gs.length ≤ 14 ∧
       (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
         w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0
               else w.getD g.2.1 0 &&& w.getD g.2.2 0])
         ([709697, 1356164, 2308120, 4543010, 11542531, 9994288, 13123596, 11141888, 13896704, 14745792, 16277519, 16351472, 16649984] : List ℕ)).getD (13 + gs.length - 1) 0 = 4095) :
    ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (14 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
    w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0
          else w.getD g.2.1 0 &&& w.getD g.2.2 0]
  have liftBits (gs : List (Bool × ℕ × ℕ)) (a b : List ℕ) (p q : ℕ)
      (len : a.length = b.length)
      (base : ∀ i : ℕ, (a.getD i 0).testBit p = true → (b.getD i 0).testBit q = true) :
      ∀ i : ℕ, ((gs.foldl step a).getD i 0).testBit p = true →
        ((gs.foldl step b).getD i 0).testBit q = true := by
    induction gs generalizing a b with
    | nil => exact base
    | cons g gs ih =>
      apply ih
      · simp [step, len]
      · intro i
        by_cases inside : i < a.length
        · have insideB : i < b.length := len ▸ inside
          simpa only [step, List.getD_append _ _ _ _ inside, List.getD_append _ _ _ _ insideB] using base i
        · by_cases last : i = a.length
          · subst i
            simp only [step, List.getD_append_right _ _ _ _ (Nat.le_refl _),
              List.getD_append_right _ _ _ _ (Nat.le_of_eq len.symm), ← len, Nat.sub_self, List.getD_cons_zero]
            cases flag : g.1 <;> simp [Nat.testBit_and, Nat.testBit_or] <;>
              grind [base g.2.1, base g.2.2]
          · have ha : (step a g).length ≤ i := by simp [step]; omega
            have hb : (step b g).length ≤ i := by simp [step]; omega
            rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
            simp
  let big : List ℕ := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
  let small : List ℕ := [709697, 1356164, 2308120, 4543010, 11542531, 9994288, 13123596, 11141888, 13896704, 14745792, 16277519, 16351472, 16649984]
  obtain ⟨gs, lower, upper, computes⟩ := circuit
  let last := 13 + gs.length - 1
  change (gs.foldl step small).getD last 0 = 4095 at computes
  refine ⟨gs, lower, upper, ?_⟩
  change (gs.foldl step big).getD last 0 = 1764784
  apply Nat.eq_of_testBit_eq
  intro r
  obtain ⟨k, label, bounds⟩ := cover r
  change ∀ i : Fin 13, if (1764784 : ℕ).testBit r then
    (small.getD i 0).testBit k = true → (big.getD i 0).testBit r = true
    else (big.getD i 0).testBit r = true → (small.getD i 0).testBit k = true at bounds
  cases hp : (1764784 : ℕ).testBit r with
  | true =>
    simp only [hp, ite_true] at bounds
    apply liftBits gs small big k r (by decide) _ last
    · rw [computes, ← label, hp]
    · intro i
      by_cases hi : i < 13
      · exact bounds ⟨i,hi⟩
      · have hout : small.length ≤ i := by change 13 ≤ i; omega
        rw [List.getD_eq_default _ _ hout]
        simp
  | false =>
    simp only [hp, Bool.false_eq_true, ite_false] at bounds
    cases hval : ((gs.foldl step big).getD last 0).testBit r with
    | false => rfl
    | true =>
      have h := liftBits gs big small r k (by decide) (fun i => by
        by_cases hi : i < 13
        · exact bounds ⟨i,hi⟩
        · have hout : big.length ≤ i := by change 13 ≤ i; omega
          rw [List.getD_eq_default _ _ hout]
          simp) last hval
      rw [computes, ← label, hp] at h
      contradiction
