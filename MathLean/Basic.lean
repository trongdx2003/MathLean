import Mathlib.Tactic

lemma aux_list_exists_last_elem (l : List Nat) (h : l.length ≥ 1) :
  ∃ x l', l = l' ++ [x] := by
  induction' l with a l
  · norm_num at h
  · rename_i h_tail
    induction l_length : l.length with
    | zero => use a, []; simp at *; exact l_length
    | succ m => obtain ⟨k, ⟨L, hL⟩⟩ := h_tail (by linarith)
                use k, a :: L
                rw [hL]
                rfl

@[simp] def isSorted : List ℕ → Prop
  | [] => True
  | _ :: [] => True
  | x :: y :: xs => if x > y then False else (isSorted (y :: xs))

theorem aux_list_sorted_by_add_one_iff (x : ℕ) (l : List ℕ) (h : l.length ≥ 1) (sortedl : isSorted l) :
  x ≥ l.getLast! ↔ isSorted (l ++ [x]) := by
    induction l_length : l.length generalizing l with
    | zero => linarith
    | succ m => rename_i hl
                cases l
                · norm_num at l_length
                · simp at l_length
                  rename_i head tail
                  cases tail
                  · simp
                  · simp at sortedl hl
                    simp
                    rename_i head' tail
                    have : (head' :: tail).getLast?.getD 0 ≤ x ↔ isSorted (head' :: tail ++ [x]) := by
                      apply hl
                      · simp
                      · exact sortedl.right
                      · exact l_length
                    tauto

theorem aux_list_sorted_right_cancel_one_elem (l : List ℕ) (x : ℕ) : isSorted (l ++ [x]) → isSorted l := by
  intro h
  induction l_length : l.length generalizing l with
  | zero => simp at l_length; rw [l_length]; trivial
  | succ m => rename_i hl
              cases l
              · norm_num at l_length
              · rename_i _ tail
                simp at l_length
                cases tail
                · trivial
                · simp
                  simp at h
                  exact ⟨h.left, hl _ h.right l_length⟩

theorem aux_list_sorted_left_cancel (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted bs := by
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length; rw [as_length] at h; simpa [h]
  | succ m => rename_i hl
              obtain ⟨x, c, hxc⟩ := aux_list_exists_last_elem as (by linarith)
              rw [hxc] at as_length h
              simp at as_length
              rw [List.append_assoc] at h
              have sorted_x_bs : isSorted ([x] ++ bs) := hl c ([x] ++ bs) h as_length
              cases bs
              · trivial
              · simp at sorted_x_bs
                exact sorted_x_bs.right

theorem aux_list_sorted_right_cancel (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted as := by
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length; rw [as_length]; trivial
  | succ m => rename_i hl
              cases as
              · trivial
              · simp at as_length
                rename_i _ tail
                cases tail
                · trivial
                · simp at h
                  simp
                  exact ⟨h.left, hl _ _ h.right as_length⟩

@[simp] def isEqual : List ℕ → List ℕ → Prop
  | [], [] => True
  | [], _ => False
  | _, [] => False
  | x :: xs, y :: ys => if x != y then False else isEqual xs ys

theorem aux_list_eq_imp_eq_by_add_one_elem (as bs : List ℕ) (h : isEqual as bs) : ∀ x, isEqual (as ++ [x]) (bs ++ [x]) := by
  intro x
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length
            simp [as_length] at *
            cases bs
            · simp
            · simp at h
  | succ m => rename_i hl
              cases as
              · norm_num at as_length
              · simp at as_length
                cases bs
                <;> simp at h
                simp
                exact ⟨h.left, hl _ _ h.right as_length⟩

theorem aux_list_eq_imp_eq_by_add_a_list (as bs : List ℕ) (h : isEqual as bs) : ∀ (cs : List ℕ), isEqual (as ++ cs) (bs ++ cs) := by
  intro cs
  induction cs_length : cs.length generalizing cs with
  | zero => simp at cs_length
            rw [cs_length]
            simp [h]
  | succ m => rename_i hl
              obtain ⟨x, cs', h_x_cs⟩ := aux_list_exists_last_elem cs (by linarith)
              rw [h_x_cs] at cs_length
              rw [h_x_cs, ← List.append_assoc, ← List.append_assoc]
              apply aux_list_eq_imp_eq_by_add_one_elem
              simp at cs_length
              exact hl cs' cs_length

theorem aux_list_add_one_eq_imp_list_eq (as bs : List ℕ) (x : ℕ) : isEqual (as ++ [x]) (bs ++ [x]) → isEqual as bs := by
  intro h
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length
            rw [as_length]
            cases bs
            · simp
            · simp [as_length] at h
  | succ m => rename_i hl
              cases as
              · norm_num at as_length
              · simp at as_length
                cases bs
                <;> simp at h
                simp
                exact ⟨h.left, hl _ _ h.right as_length⟩

theorem aux_list_add_list_eq_imp_list_eq (as bs cs : List ℕ) : isEqual (as ++ cs) (bs ++ cs) → isEqual as bs := by
  intro h
  induction cs_length : cs.length generalizing cs with
  | zero => simp at cs_length
            rw [cs_length] at h
            simp at h
            exact h
  | succ m => rename_i hl
              obtain ⟨x, cs', h_x_cs⟩ := aux_list_exists_last_elem cs (by linarith)
              rw [h_x_cs] at cs_length h
              rw [← List.append_assoc, ← List.append_assoc] at h
              apply aux_list_add_one_eq_imp_list_eq at h
              simp at cs_length
              exact hl cs' h cs_length

@[simp] def List.ge_list : List ℕ → List ℕ → Prop
  | [], _ => False
  | _, [] => False
  | [x], [y] => if x ≥ y then True else False
  | x :: xs, y :: ys => if x < y then False else xs.ge_list ys

theorem aux_list_ge_def (as bs : List ℕ) (x y : ℕ) (non_empty : as ≠ [] ∧ bs ≠ []) : (x :: as).ge_list (y :: bs) → x ≥ y ∧ as.ge_list bs := by
  intro h
  simp [non_empty] at h
  exact h

theorem aux_list_ge_list_of_same_length (as bs : List ℕ) : as.ge_list bs → as.length = bs.length := by
  intro h
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length; simp [as_length] at h
  | succ m => rename_i hl
              cases as
              · norm_num at as_length
              · simp at as_length
                cases bs
                · simp at h
                · rename_i _ tail _ tail'
                  cases tail <;> cases tail'
                  · simp at *
                    exact as_length.symm
                  · simp at h
                  · simp at h
                  · simp at h
                    rw [List.length, Nat.succ_inj]
                    exact hl _ _ h.right as_length

theorem aux_list_ge_list_trans (as bs cs : List ℕ) (as_ge_bs : as.ge_list bs) (bs_ge_cs : bs.ge_list cs) : as.ge_list cs := by
  induction bs_length : bs.length generalizing as bs cs with
  | zero => simp at bs_length; simp [bs_length] at bs_ge_cs
  | succ m => rename_i h
              cases bs
              · simp at bs_ge_cs
              · rename_i tail_bs
                simp at bs_length
                cases m
                · simp at bs_length
                  rw [bs_length] at as_ge_bs bs_ge_cs
                  cases as
                  · simp at as_ge_bs
                  · rename_i tail_as
                    cases tail_as
                    · cases cs
                      · simp at bs_ge_cs
                      · rename_i tail_cs
                        cases tail_cs
                        · simp at *
                          exact bs_ge_cs.trans as_ge_bs
                        · simp at bs_ge_cs
                    · simp at as_ge_bs
                · have non_empty_tail_bs : tail_bs ≠ [] := List.length_pos_iff.1 (by linarith)
                  cases as
                  · simp at as_ge_bs
                  · rename_i tail_as
                    have non_empty_tail_as : tail_as ≠ [] := by
                      apply aux_list_ge_list_of_same_length at as_ge_bs
                      simp at as_ge_bs
                      exact List.length_pos_iff.1 (by linarith)
                    cases cs
                    · simp at bs_ge_cs
                    · rename_i tail_cs
                      have non_empty_tail_cs : tail_cs ≠ [] := by
                        apply aux_list_ge_list_of_same_length at bs_ge_cs
                        simp at bs_ge_cs
                        exact List.length_pos_iff.1 (by linarith)
                      apply aux_list_ge_def _ _ _ _ ⟨non_empty_tail_as, non_empty_tail_bs⟩ at as_ge_bs
                      apply aux_list_ge_def _ _ _ _ ⟨non_empty_tail_bs, non_empty_tail_cs⟩ at bs_ge_cs
                      simp [non_empty_tail_as, non_empty_tail_cs]
                      exact ⟨by linarith, h _ _ _ as_ge_bs.right bs_ge_cs.right bs_length⟩

@[simp] def List.ge_nat : List ℕ → ℕ → Prop
  | [], _ => False
  | [x], y => if x < y then False else True
  | x :: xs, y => if x < y then False else xs.ge_nat y

example : [1].ge_nat 0 := trivial

example : [3, 5].ge_nat 2 := trivial

theorem aux_list_ge_nat_trans (as bs : List ℕ) (c : ℕ) : as.ge_list bs → bs.ge_nat c → as.ge_nat c := by
  intros as_ge_bs bs_ge_c
  induction bs_length : bs.length generalizing as bs with
  | zero => simp at bs_length
            simp [bs_length] at bs_ge_c
  | succ m => rename_i h
              cases bs
              · norm_num at bs_length
              · simp at bs_length
                rename_i tail
                cases as
                · simp at as_ge_bs
                · rename_i tail'
                  cases tail <;> cases tail'
                  · simp at *; linarith
                  · simp at as_ge_bs
                  · simp at as_ge_bs
                  · simp [-List.length_cons] at *
                    exact ⟨by linarith, h _ _ as_ge_bs.right bs_ge_c.right bs_length⟩


@[simp] def List.add_nat : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, c => (x + c) :: (add_nat xs c)

example : [1, 2].add_nat 3 = [4, 5] := rfl

theorem aux_list_add_nat_ge_list_add_nat (as bs : List ℕ) (c d : ℕ) (non_empty_as : as ≠ []) (non_empty_bs : bs ≠ []):
  as.ge_list bs → c ≥ d → (as.add_nat c).ge_list (bs.add_nat d) := by
    intro as_ge_bs c_ge_d
    induction bs_length : bs.length generalizing as bs with
    | zero => simp at bs_length
              contradiction
    | succ m => rename_i h
                cases bs
                · norm_num at bs_length
                · simp at bs_length
                  cases as
                  · contradiction
                  · rename_i _ tail_bs _ tail_as
                    cases tail_bs <;> cases tail_as
                    <;> try (simp at as_ge_bs)
                    <;> simp
                    · linarith
                    · exact ⟨by linarith, h _ _ (List.length_pos_iff.1 (by norm_num)) (List.length_pos_iff.1 (by norm_num)) as_ge_bs.right bs_length⟩
