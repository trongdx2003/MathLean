-- -- This module serves as the root of the `MathLean` library.
-- -- Import modules here that should be built as part of the library.
-- import Mathlib.Tactic

-- theorem identical_seq (u v : ℕ → ℕ) (h1 : u 0 = v 0) (h2 : u 1 = v 1)
--   (h3 : ∀ n, u (n + 2) = u (n + 1) + u n) (h4 : ∀ n, v (n + 2) = v (n + 1) + v n) :
--     ∀ n, u n = v n := by
--     intro n
--     induction' n using Nat.strong_induction_on with n hn
--     cases n with
--     | zero => exact h1
--     | succ k => cases k with
--                 | zero => rw [zero_add, h2]
--                 | succ l => have : l + 1 + 1 = l + 2 := rfl
--                             rw [this] at *
--                             rw [h3 l, h4 l, hn (l + 1) (by linarith), hn l (by linarith)]

-- -- def fib_recursive : Nat → Nat
-- -- | 0 => 0
-- -- | 1 => 1
-- -- | n + 2 => fib_recursive (n + 1) + fib_recursive n

-- -- def fib_iter (n : Nat) : Nat :=
-- --   let rec l (i a b : Nat) :=
-- --     match i with
-- --     | 0 => a
-- --     | i' + 1 => l i' b (a + b)
-- --   l n 0 1


-- -- theorem aux (m : ℕ) : fib_iter (m + 2) = fib_iter (m + 1) + fib_iter m := by
-- --   have h (n x y : ℕ) : fib_iter.l n (x + y) (x + 2 * y) =
-- --     fib_iter.l n y (x + y) + fib_iter.l n x y := by
-- --     induction n generalizing x y with
-- --     | zero => repeat rw [fib_iter.l]
-- --               exact Nat.add_comm x y
-- --     | succ k => repeat rw [fib_iter.l]
-- --                 rename_i h
-- --                 rw [← h y (x + y)]
-- --                 congr 1
-- --                 <;> ring
-- --   repeat rw [fib_iter]
-- --   have h1 : fib_iter.l (m + 2) 0 1 = fib_iter.l m 1 2 := rfl
-- --   have h2 : fib_iter.l (m + 1) 0 1 = fib_iter.l m 1 1 := rfl
-- --   rw [h1, h2]
-- --   exact h m 0 1

-- -- example (n : ℕ) : fib_recursive n = fib_iter n := by
-- --   apply identical_seq
-- --   · rfl
-- --   · rfl
-- --   · intro n; rfl
-- --   · intro n; exact aux n


-- example (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h₂ : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
--   a + b + c = 2 + Real.sqrt ((2 - a) * (2 - b) * (2 - c)) := by
--     have h₃ : (a + b + c - 2) ^ 2 = (2 - a) * (2 - b) * (2 - c) := by linarith
--     have h₄ : a + b + c - 2 ≥ 0 := by
--       have h₄₁: 2 - a ≥ 0 := by
--         have : a ^ 2 ≤ 4 := by calc
--           a ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + a * b * c := by nlinarith [mul_nonneg ha hb]
--           _ = 4 := by rw [h₂]
--         nlinarith
--       have : (a + b + c) ^ 2 ≥ 2 ^ 2 := by calc
--         (a + b + c) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c) + 2 * (a * b) + (b * c) * (2 - a) + 2 * (a * c) := by ring
--         _ = 4 + 2 * (a * b) + (b * c) * (2 - a) + 2 * (a * c) := by rw [h₂]
--         _ ≥ 4 + 0 + 0 + 0 := by linarith only [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg (mul_nonneg hb hc) h₄₁]
--         _ = 2 ^ 2 := by ring
--       nlinarith
--     have h₅ : (2 - a) * (2 - b) * (2 - c) ≥ 0 := by nlinarith
--     symm at h₃
--     rw [← Real.sqrt_eq_iff_eq_sq h₅ h₄] at h₃
--     symm at h₃
--     linarith only [h₃]


-- example (m n k : ℕ) (h : m ^ 2 + n = k ^ 2 + k) : n ≥ m := by
--   have : k ≥ m := by nlinarith
--   nlinarith

-- -- example (x y z : ℝ) (h : x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1) : 16 * x * y * z * (x * y + y * z + z * x) - (x * y + y * z + z * x) - 9 * (x * y * z) ^ 2 + 23 * x * y * z + 1 ≥ 0 := by
-- --   nlinarith [sq_nonneg (3 * x - 1), sq_nonneg (3 * y - 1), sq_nonneg (3 * z - 1)]


-- -- example (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3) :
-- --   a ^ 2 + b ^ 2 + c ^ 2 + a * b * c ≥ 4 := by
-- --     nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

-- -- def isSorted {α : Type} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] : List α → Prop
-- --   | [] => True
-- --   | _ :: [] => True
-- --   | x :: y :: xs => if x > y then False else (isSorted (y :: xs))

-- -- def bubblePass : List Nat → List Nat
-- --   | []            => []
-- --   | [x]           => [x]
-- --   | x :: y :: xs  =>
-- --       if x ≤ y then
-- --         x :: bubblePass (y :: xs)
-- --       else
-- --         y :: bubblePass (x :: xs)

-- -- def bubbleSortAux : Nat → List Nat → List Nat
-- --   | 0,   l => l
-- --   | n+1, l => bubbleSortAux n (bubblePass l)

-- -- def bubbleSort (l : List Nat) : List Nat :=
-- --   bubbleSortAux (l.length - 1) l

-- -- example (l : List Nat) : isSorted (bubbleSort l) := by
-- --   cases l
-- --   · trivial
-- --   · rename_i head tail
-- --     sorry

-- lemma aux_listLengthAtLeast1 (l : List Nat) (h : l.length ≥ 1) :
--   ∃ x l', l = l' ++ [x] := by
--   induction' l with a l
--   · norm_num at h
--   · rename_i h_tail
--     induction l_length : l.length with
--     | zero => use a, []; simp at *; exact l_length
--     | succ m => obtain ⟨k, ⟨L, hL⟩⟩ := h_tail (by linarith)
--                 use k, a :: L
--                 rw [hL]
--                 rfl


-- @[simp] def isSorted : List ℕ → Prop
--   | [] => True
--   | _ :: [] => True
--   | x :: y :: xs => if x > y then False else (isSorted (y :: xs))


-- lemma aux_sortedList (x : ℕ) (l : List ℕ) (h : l.length ≥ 1) (sortedl : isSorted l) :
--   x ≥ l.getLast! ↔ isSorted (l ++ [x]) := by
--     induction l_length : l.length generalizing l with
--     | zero => linarith
--     | succ m => rename_i hl
--                 cases l
--                 · norm_num at l_length
--                 · simp at l_length
--                   rename_i head tail
--                   cases tail
--                   · simp
--                   · simp at sortedl hl
--                     simp
--                     rename_i head' tail
--                     have : (head' :: tail).getLast?.getD 0 ≤ x ↔ isSorted (head' :: tail ++ [x]) := by
--                       apply hl
--                       · simp
--                       · exact sortedl.right
--                       · exact l_length
--                     tauto


-- lemma aux_sortedList2 (l : List ℕ) (x : ℕ) : isSorted (l ++ [x]) → isSorted l := by
--   intro h
--   induction l_length : l.length generalizing l with
--   | zero => simp at l_length; rw [l_length]; trivial
--   | succ m => rename_i hl
--               cases l
--               · norm_num at l_length
--               · rename_i _ tail
--                 simp at l_length
--                 cases tail
--                 · trivial
--                 · simp
--                   simp at h
--                   exact ⟨h.left, hl _ h.right l_length⟩


-- lemma aux_SortedList3 (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted bs := by
--   induction as_length : as.length generalizing as bs with
--   | zero => simp at as_length; rw [as_length] at h; simpa [h]
--   | succ m => rename_i hl
--               obtain ⟨x, c, hxc⟩ := aux_listLengthAtLeast1 as (by linarith)
--               rw [hxc] at as_length h
--               simp at as_length
--               rw [List.append_assoc] at h
--               have sorted_x_bs : isSorted ([x] ++ bs) := hl c ([x] ++ bs) h as_length
--               cases bs
--               · trivial
--               · simp at sorted_x_bs
--                 exact sorted_x_bs.right


-- lemma aux_SortedList4 (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted as := by
--   induction as_length : as.length generalizing as bs with
--   | zero => simp at as_length; rw [as_length]; trivial
--   | succ m => rename_i hl
--               cases as
--               · trivial
--               · simp at as_length
--                 rename_i _ tail
--                 cases tail
--                 · trivial
--                 · simp at h
--                   simp
--                   exact ⟨h.left, hl _ _ h.right as_length⟩

-- @[simp] def isEqual : List ℕ → List ℕ → Prop
--   | [], [] => True
--   | [], _ => False
--   | _, [] => False
--   | x :: xs, y :: ys => if x != y then False else isEqual xs ys


-- lemma aux_list_eq_imp_eq_by_add_one_elem (as bs : List ℕ) (h : isEqual as bs) : ∀ x, isEqual (as ++ [x]) (bs ++ [x]) := by
--   intro x
--   induction as_length : as.length generalizing as bs with
--   | zero => simp at as_length
--             simp [as_length] at *
--             cases bs
--             · simp
--             · simp at h
--   | succ m => rename_i hl
--               cases as
--               · norm_num at as_length
--               · simp at as_length
--                 cases bs
--                 · simp at h
--                 · simp at h
--                   simp
--                   exact ⟨h.left, hl _ _ h.right as_length⟩

-- lemma aux_list_eq_imp_eq_by_add_a_list (as bs : List ℕ) (h : isEqual as bs) : ∀ (cs : List ℕ), isEqual (as ++ cs) (bs ++ cs) := by
--   intro cs
--   induction cs_length : cs.length generalizing cs with
--   | zero => simp at cs_length
--             rw [cs_length]
--             simp [h]
--   | succ m => rename_i hl
--               obtain ⟨x, cs', h_x_cs⟩ := aux_listLengthAtLeast1 cs (by linarith)
--               rw [h_x_cs] at cs_length
--               rw [h_x_cs, ← List.append_assoc, ← List.append_assoc]
--               apply aux_list_eq_imp_eq_by_add_one_elem
--               simp at cs_length
--               exact hl cs' cs_length

-- lemma aux_list_add_one_eq_imp_list_eq (as bs : List ℕ) (x : ℕ) : isEqual (as ++ [x]) (bs ++ [x]) → isEqual as bs := by
--   intro h
--   induction as_length : as.length generalizing as bs with
--   | zero => simp at as_length
--             rw [as_length]
--             cases bs
--             · simp
--             · simp [as_length] at h
--   | succ m => rename_i hl
--               cases as
--               · norm_num at as_length
--               · simp at as_length
--                 cases bs
--                 · simp at h
--                 · simp at h
--                   simp
--                   exact ⟨h.left, hl _ _ h.right as_length⟩

-- lemma aux_list_add_list_eq_imp_list_eq (as bs cs : List ℕ) : isEqual (as ++ cs) (bs ++ cs) → isEqual as bs := by
--   intro h
--   induction cs_length : cs.length generalizing cs with
--   | zero => simp at cs_length
--             rw [cs_length] at h
--             simp at h
--             exact h
--   | succ m => rename_i hl
--               obtain ⟨x, cs', h_x_cs⟩ := aux_listLengthAtLeast1 cs (by linarith)
--               rw [h_x_cs] at cs_length h
--               rw [← List.append_assoc, ← List.append_assoc] at h
--               apply aux_list_add_one_eq_imp_list_eq at h
--               simp at cs_length
--               exact hl cs' h cs_length
